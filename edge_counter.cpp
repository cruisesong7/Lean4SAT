#include <iostream>
#include <sstream>
#include <string>
#include <lean/lean.h>

extern "C" lean_object* readInput_Str(lean_object* w);
extern "C" lean_object* edgesExceedBound(lean_object* w, lean_object* upperbound);

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
    lean_object* w = readInput_Str(input_str);
    lean_dec_ref(input_str);

    // Define an upperbound for edge count (you can adjust this value as needed)
    lean_object* upperbound = lean_unsigned_to_nat(3);  // Example: 3 as upperbound
    lean_object* output = edgesExceedBound(w, upperbound);

    if (lean_is_scalar(output)) {
        // Output just the result as a single number (1 for exceed, 0 for not exceed)
        uint8_t result = lean_unbox(output);
        std::cout << (int)result << std::endl;
    } else {
        std::cout << "Error: Invalid result from edgesExceedBound" << std::endl;
    }

    // Clean up
    lean_dec_ref(upperbound);
    lean_dec_ref(output);
    // We're not cleaning up w here

    return 0;
}