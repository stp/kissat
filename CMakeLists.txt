# Library build for STP. The upstream configure/make build remains available.
cmake_minimum_required(VERSION 3.16)
project(kissat LANGUAGES C)

include(GNUInstallDirs)
option(BUILD_SHARED_LIBS "Build the Kissat library as a shared library" OFF)
option(BUILD_TESTING "Build incremental API tests" OFF)
option(KISSAT_BUILD_CLI "Build the standalone Kissat executable" ON)
set(KISSAT_IDENTIFIER "" CACHE STRING "Source revision recorded in the library")

if(MSVC)
    message(FATAL_ERROR "Kissat requires a POSIX C toolchain")
endif()

file(READ "${CMAKE_CURRENT_SOURCE_DIR}/VERSION" KISSAT_VERSION)
string(STRIP "${KISSAT_VERSION}" KISSAT_VERSION)
set(_kissat_identifier "${KISSAT_IDENTIFIER}")
if(NOT _kissat_identifier)
    find_package(Git QUIET)
    if(Git_FOUND)
        execute_process(COMMAND "${GIT_EXECUTABLE}" rev-parse HEAD
            WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
            OUTPUT_VARIABLE _kissat_identifier OUTPUT_STRIP_TRAILING_WHITESPACE
            ERROR_QUIET)
    endif()
endif()
if(NOT _kissat_identifier)
    set(_kissat_identifier "unknown")
endif()
set(KISSAT_COMPILER "${CMAKE_C_COMPILER_ID} ${CMAKE_C_COMPILER_VERSION}")
set(KISSAT_BUILD "CMake ${CMAKE_SYSTEM_NAME} ${CMAKE_SYSTEM_PROCESSOR}")
configure_file(cmake/build.h.in build.h @ONLY)

file(GLOB KISSAT_SOURCES CONFIGURE_DEPENDS "src/*.c")
set(KISSAT_APPLICATION_SOURCES
    src/application.c src/handle.c src/parse.c src/witness.c)
foreach(_source IN LISTS KISSAT_APPLICATION_SOURCES)
    list(REMOVE_ITEM KISSAT_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/${_source}")
endforeach()
list(REMOVE_ITEM KISSAT_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/main.c")

function(kissat_configure_target target)
    set_target_properties(${target} PROPERTIES
        C_STANDARD 99 C_STANDARD_REQUIRED YES POSITION_INDEPENDENT_CODE ON)
    target_include_directories(${target} PRIVATE
        "${CMAKE_CURRENT_SOURCE_DIR}/src" "${CMAKE_CURRENT_BINARY_DIR}")
    target_compile_definitions(${target} PRIVATE STATISTICS
        "$<$<CONFIG:Debug>:LOGGING>" "$<$<CONFIG:Debug>:METRICS>"
        "$<$<CONFIG:Debug>:EMBEDDED>")
    # Clients may throw from allocator callbacks. Unwind every C frame so
    # they can discard a partial solver and release its owned allocations.
    if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang")
        target_compile_options(${target} PRIVATE -fexceptions)
    endif()
    if(UNIX)
        target_link_libraries(${target} PRIVATE m)
    endif()
endfunction()

add_library(kissat ${KISSAT_SOURCES})
kissat_configure_target(kissat)
target_include_directories(kissat PUBLIC
    "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/src>"
    "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}/kissat>")
add_library(Kissat::Kissat ALIAS kissat)
install(TARGETS kissat
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}")
install(FILES src/kissat.h DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/kissat")

if(KISSAT_BUILD_CLI)
    add_executable(kissat-bin src/main.c ${KISSAT_APPLICATION_SOURCES})
    set_target_properties(kissat-bin PROPERTIES OUTPUT_NAME kissat)
    kissat_configure_target(kissat-bin)
    target_link_libraries(kissat-bin PRIVATE kissat)
    install(TARGETS kissat-bin RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}")
endif()

if(BUILD_TESTING)
    enable_testing()
    enable_language(CXX)
    find_package(Python3 REQUIRED COMPONENTS Interpreter)
    if(BUILD_SHARED_LIBS)
        set(_kissat_test_library kissat)
    else()
        # ctypes needs a shared library; keep the installed library static.
        add_library(kissat-test SHARED ${KISSAT_SOURCES})
        kissat_configure_target(kissat-test)
        set(_kissat_test_library kissat-test)
    endif()
    foreach(_reuse RANGE 0 2)
        add_test(NAME incremental-api-reuse-${_reuse}
            COMMAND "${CMAKE_COMMAND}" -E env "KISSAT_TEST_OPTIONS=incrementalreuse=${_reuse}"
                "${Python3_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/test/incremental.py"
                --library "$<TARGET_FILE:${_kissat_test_library}>" --cases 500)
        set_tests_properties(incremental-api-reuse-${_reuse}
            PROPERTIES TIMEOUT 180 LABELS incremental)
    endforeach()
    add_executable(kissat-allocator-test test/allocator.cpp)
    target_compile_features(kissat-allocator-test PRIVATE cxx_std_17)
    target_link_libraries(kissat-allocator-test PRIVATE kissat)
    add_test(NAME allocator-failure COMMAND kissat-allocator-test)
    set_tests_properties(allocator-failure PROPERTIES TIMEOUT 30 LABELS incremental)
endif()
