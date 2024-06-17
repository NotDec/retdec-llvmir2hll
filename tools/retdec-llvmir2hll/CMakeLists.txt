add_executable(retdec-llvmir2hll-exe
  retdec-llvmir2hll.cpp
)

if(NOT LLVM_ENABLE_RTTI)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

target_link_libraries(retdec-llvmir2hll-exe 
  retdec::llvmir2hll
)

set_target_properties(retdec-llvmir2hll-exe
	PROPERTIES
		OUTPUT_NAME "retdec-llvmir2hll"
)

install(TARGETS retdec-llvmir2hll-exe DESTINATION ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})
