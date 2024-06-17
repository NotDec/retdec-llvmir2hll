add_subdirectory(notdec-llvm2c)

if(NOTDEC_ENABLE_RETDEC_LLVMIR2HLL)
    add_subdirectory(retdec-llvmir2hll)
endif()
