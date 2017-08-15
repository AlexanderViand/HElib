cmake_minimum_required(VERSION 3.8)
project(fhe)

option(NO_HALF_SIZE_PRIME  "tells helib to not use the half size primes in the prime chain" OFF)

option(FHE_THREADS
        "tells helib to enable generic multithreading capabilities; must be used with a thread-enabled NTL" ON)

include("CMakeDependentOption")

cmake_dependent_option(FHE_BOOT_THREADS "tells helib to use a multithreading strategy for bootstrapping; requires DFHE_THREADS (see above)" ON
        "FHE_THREADS" OFF)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -g -Og -Wfatal-errors -Wshadow -Wall")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3")


if(FHE_THREADS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pthread -DFHE_THREADS" )
endif(FHE_THREADS)

if(FHE_BOOT_THREADS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DFHE_BOOT_THREADS" )
endif(FHE_BOOT_THREADS)

if(NO_HALF_SIZE_PRIME)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DNO_HALF_SIZE_PRIME" )
endif(NO_HALF_SIZE_PRIME)


set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/../cmake/Modules/")
find_package(GMP REQUIRED)
find_package(NTL REQUIRED)

set(SOURCE_FILES
        BenesNetwork.cpp
        blockMatmul.cpp
        blockMatmul1D.cpp
        bluestein.cpp
        bluestein.h
        cgauss.cpp
        cloned_ptr.h
        CModulus.cpp
        CModulus.h
        Ctxt.cpp
        Ctxt.h
        debugging.cpp
        DoubleCRT.cpp
        DoubleCRT.h
        EncryptedArray.cpp
        EncryptedArray.h
        eqtesting.cpp
        EvalMap.cpp
        EvalMap.h
        extractDigits.cpp
        FHE.cpp
        FHE.h
        FHEContext.cpp
        FHEContext.h
        hypercube.cpp
        hypercube.h
        IndexMap.h
        IndexSet.cpp
        IndexSet.h
        KeySwitching.cpp
        matching.cpp
        matching.h
        matmul.cpp
        matmul.h
        matmul1D.cpp
        multicore.h
        MulTime.cpp
        NumbTh.cpp
        NumbTh.h
        OptimizePermutations.cpp
        PAlgebra.cpp
        PAlgebra.h
        params.cpp
        PermNetwork.cpp
        permutations.cpp
        permutations.h
        polyEval.cpp
        polyEval.h
        powerful.cpp
        powerful.h
        recryption.cpp
        recryption.h
        replicate.cpp
        replicate.h
        timing.cpp
        timing.h)

add_library(fhe ${SOURCE_FILES})
target_link_libraries(fhe m gmp ntl)


### INSTALLATION

set(HEADER_FILES ${SOURCE_FILES})
list(FILTER HEADER_FILES INCLUDE REGEX ".+\\.h?h$")

install(TARGETS fhe DESTINATION lib)
install(FILES ${HEADER_FILES} DESTINATION include/FHE)

add_custom_target(install_${PROJECT_NAME}
        $(MAKE) install
        DEPENDS fhe
        COMMENT "Installing ${PROJECT_NAME}")

### Testing
enable_testing()

set (TEST_SOURCE_FILES
        Test_bootstrapping.cpp
        Test_EvalMap.cpp
        Test_extractDigits.cpp
        Test_General.cpp
        Test_IO.cpp
        Test_LinPoly.cpp
        Test_matmul.cpp
        Test_matmul1D.cpp
        Test_PAlgebra.cpp
        Test_Permutations.cpp
        Test_PolyEval.cpp
        Test_Replicate.cpp )

foreach(testsourcefile ${TEST_SOURCE_FILES})
    string( REPLACE ".cpp" "_x" testname ${testsourcefile} )
    add_executable( ${testname} ${testsourcefile} )
    target_link_libraries( ${testname} m gmp ntl fhe )
endforeach(testsourcefile ${TEST_SOURCE_FILES})

add_test(test_general_1 Test_General_x  R=1 k=10 p=2 r=2 noPrint=1)
add_test(test_general_2 Test_General_x  R=1 k=10 p=2 d=2 noPrint=1)
add_test(test_general_3 Test_General_x  R=2 k=10 p=7 r=2 noPrint=1)
add_test(test_matmul    Test_matmul_x   m=1365)
add_test(test_matmul1D  Test_matmul1D_x m=96 p=7)
add_test(test_linpoly   Test_LinPoly_x  noPrint=1)
add_test(test_permutations Test_Permutations_x  noPrint=1)
add_test(test_polyeval  Test_PolyEval_x p=7 r=2 d=34 noPrint=1)
add_test(test_replicate Test_Replicate_x    m=1247 noPrint=1)
add_test(test_evalmap   Test_EvalMap_x  mvec="[7 3 221]" gens="[3979 3095 3760]" ords="[6 2 -8]" noPrint=1)
add_test(test_extractdigits Test_extractDigits_x    m=2047 p=5 noPrint=1)
add_test(test_bootstrapping_1 Test_bootstrapping_x  noPrint=1)
add_test(test_bootstrapping_2 Test_bootstrapping_x  p=7 noPrint=1)

set(tests
        test_general_1
        test_general_2
        test_general_3
        test_matmul
        test_matmul1D
        test_linpoly
        test_permutations
        test_polyeval
        test_replicate
        test_evalmap
        test_extractdigits
        test_bootstrapping_1
        test_bootstrapping_2
        )

# Tests are considered passed if no "bad" words appear in the output
set_tests_properties(${tests} PROPERTIES
        FAIL_REGULAR_EXPRESSION "Error;ERROR;Failed;failed;BAD;bad"
        )