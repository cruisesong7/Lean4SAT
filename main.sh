#!/bin/bash

[ "$1" = "-h" -o "$1" = "--help" ] && echo "
Description:
    Updated on 2024-03-19
    This script generates SAT encodings for Ramsey graph problems.

Usage:
    ./main.sh [options] n p q

Example:
    # Generate encoding for R(3,7) on 23 vertices with vertex degrees between 5 and 6
    ./main.sh -d 5 -D 6 23 3 7
    
    # Using different encodings for vertex degrees and edge count constraints
    ./main.sh -d 5 -D 6 --deg-card totalizer --edge-lb 80 --edge-ub 85 --edge-card sinz 23 3 7

Required Arguments:
    n               Number of vertices in the graph
    p               Number of colour 1 cliques to block in encoding
    q               Number of colour 2 cliques to block in encoding

Options:
    -d INT          Lower bound on number of (colour 1) edges per vertex
    -D INT          Upper bound on number of (colour 1) edges per vertex
    -E INT          Upper bound on monochromatic triangles on colour 1 edges
    -F INT          Upper bound on monochromatic triangles on colour 2 edges
    -P              Include maximum p-clique free constraints
    --deg-card TYPE Cardinality encoding type for degree constraints (sinz, totalizer, totalizerconcise default: sinz)
    --edge-lb INT   Lower bound on total number of edges
    --edge-ub INT   Upper bound on total number of edges
    --edge-card TYPE Cardinality encoding type for edge constraints (sinz, totalizer, totalizerconcise default: sinz)
    --strict-degree-bound  Use degree bounds calculated from known Ramsey numbers
" && exit

# Add new variables for the new parameters
deg_card_type="sinz"
edge_card_type="sinz"
edge_lb=0
edge_ub=0
lower=0
upper=0
Edge_b=0
Edge_r=0
mpcf=0
strict_degree_bound=0

# Parse arguments
while [ $# -gt 0 ]; do
    case "$1" in
        -d) lower="$2"; shift ;;
        -D) upper="$2"; shift ;;
        -E) Edge_b="$2"; shift ;;
        -F) Edge_r="$2"; shift ;;
        -P) mpcf="MPCF" ;;
        --deg-card) deg_card_type="$2"; shift ;;
        --edge-lb) edge_lb="$2"; shift ;;
        --edge-ub) edge_ub="$2"; shift ;;
        --edge-card) edge_card_type="$2"; shift ;;
        --strict-degree-bound) 
            strict_degree_bound=1
            ;;
        -*) echo "Invalid option: $1" >&2; exit 1 ;;
        *) break ;;
    esac
    shift
done

# Validate required arguments
if [ -z "$1" ] || [ -z "$2" ] || [ -z "$3" ]
then
    echo "Need instance order (number of vertices) and p, q values. Use -h or --help for further instruction"
    exit 1
fi

n=$1 #order
p=$2
q=$3

# Calculate strict degree bounds if requested
if [ "$strict_degree_bound" -eq 1 ]; then
    bounds=$(python3 -c "from gen_instance.ramsey_bounds import calculate_strict_bounds; l,u = calculate_strict_bounds(int('$n'),int('$p'),int('$q')); print(f'{l} {u}')")
    lower=$(echo $bounds | cut -d' ' -f1)
    upper=$(echo $bounds | cut -d' ' -f2)
fi

# Validate numeric values
if ! [[ "$lower" =~ ^[0-9]+$ ]] || ! [[ "$upper" =~ ^[0-9]+$ ]]; then
    echo "Error: Degree bounds must be non-negative integers"
    exit 1
fi

# Generate instance name
cnf="constraints_${n}_${p}_${q}_${lower}_${upper}_${Edge_b}_${Edge_r}_${mpcf}"
if [ "$lower" -gt 0 ] || [ "$upper" -gt 0 ]; then
    cnf="${cnf}_deg${deg_card_type}"
fi
if [ "$edge_lb" -gt 0 ] || [ "$edge_ub" -gt 0 ]; then
    cnf="${cnf}_edge${edge_card_type}_lb${edge_lb}_ub${edge_ub}"
fi

# Generate instance if it doesn't exist
if [ -f ${cnf} ]; then
    echo "Instance already exists: ${cnf}"
else
    echo "Generating instance..."
    python3 gen_instance/generate.py $n $p $q $lower $upper $Edge_b $Edge_r $mpcf $deg_card_type $edge_card_type $edge_lb $edge_ub
    echo "Generated instance: ${cnf}"
fi
