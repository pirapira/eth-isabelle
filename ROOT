session "deed" = "HOL" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
    "~~/src/HOL/Word/Word"
    "~~/src/HOL/Data_Structures/AVL_Map"
    KEC
    (* Bar *)
  theories
    ContractEnv
    Instructions
    ContractSem
    RelationalSem
    "example/Deed"
  document_files
    "root.tex"

session "all" = "HOL" +
  theories [document = false]
    "~~/src/HOL/Word/Word"
    "~~/src/HOL/Data_Structures/AVL_Map"
    KEC
    FunctionalCorrectness
    Parse
    ContractEnv
    Instructions
    ContractSem
    RelationalSem
    HP
    YellowPaper
    "example/Optimization"
    "example/AlwaysFail"
    "example/FailOnReentrance"
    "example/Deed"
