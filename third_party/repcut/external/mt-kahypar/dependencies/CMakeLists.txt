target_include_directories(MtKaHyPar-Include INTERFACE
  ${CMAKE_CURRENT_SOURCE_DIR}
)

if(KAHYPAR_USE_GROWT)
  target_compile_definitions(MtKaHyPar-BuildFlags INTERFACE KAHYPAR_USE_GROWT)
  target_link_libraries(MtKaHyPar-BuildFlags INTERFACE
      $<$<NOT:$<CXX_COMPILER_ID:MSVC>>:atomic>
  )
endif()
