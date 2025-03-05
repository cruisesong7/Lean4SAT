#include <iostream>
#include <sstream>
#include <string>
#include <lean/lean.h>

extern "C" lean_object* readInput1(lean_object* w);
extern "C" lean_object* countEdges(lean_object* w);

extern "C" void lean_initialize_runtime_module();
extern "C" void lean_initialize();
extern "C" void lean_io_mark_end_initialization();
extern "C" lean_object* initialize_Leansat(uint8_t builtin, lean_object* w);

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <space-separated numbers>" << std::endl;
        return 1;
    }

    // Combine all arguments into a single string
    std::stringstream ss;
    for (int i = 1; i < argc; ++i) {
        if (i > 1) ss << " ";
        ss << argv[i];
    }
    std::string input_string = ss.str();

    lean_initialize_runtime_module();
    lean_initialize();
    
    lean_object* res = initialize_Leansat(1, lean_io_mk_world());
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
    } else {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_io_mark_end_initialization();

    lean_object* input_str = lean_mk_string(input_string.c_str());
    lean_object* w = readInput1(input_str);
    lean_dec_ref(input_str);

    // lean_object* n = lean_unsigned_to_nat(4);  // Assuming 4 vertices, adjust if needed
    // lean_object* output = isEdgesGT(w, n);

    lean_object* output = countEdges(w);

    if (lean_is_scalar(output)) {
        uint32_t result = lean_uint32_of_nat(output);
        std::cout << "Number of edges: " << result << std::endl;
    } else {
        std::cout << "Error: Invalid result from countEdges" << std::endl;
    }

    // Clean up
    // We're not cleaning up w, n, and output_tri here

    return 0;
}