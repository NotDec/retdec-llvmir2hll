
add_subdirectory(notdec-llvm2c)

if(NOTDEC_ENABLE_RETDEC_LLVMIR2HLL)
    # remove -fno-rtti
    # string(REPLACE " -fno-rtti" "" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    add_subdirectory(retdec-llvmir2hll)
    # set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
    # enable retdec interface in notdec
    target_compile_definitions(notdec-llvm2c PUBLIC ENABLE_RETDEC_LLVMIR2HLL)
endif()
