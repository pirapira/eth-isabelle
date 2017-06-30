session "deed" = "HOL" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
    "~~/src/HOL/Word/Word"
    "~~/src/HOL/Data_Structures/AVL_Map"
    "lem/Lem_bool"
    "lem/Lem_basic_classes"
    "lem/Lem_tuple"
    "lem/Lem_function"
    "lem/Lem_maybe"
    "lem/Lem_num"
    "lem/LemExtraDefs"
    "lem/Lem_set_helpers"
    "lem/Lem_map"
    "lem/Lem_string"
    "lem/Lem_word"
    "lem/Lem_show"
    "lem/Lem_sorting"
    "lem/Lem_relation"
    "lem/Lem_pervasives"
    "lem/Word256"
    "lem/Word160"
    "lem/Word8"
    "lem/Keccak"
    "lem/Evm"
  theories
    ContractSem
    RelationalSem
  document_files
    "root.tex"

session "simplewallet" = "HOL" +
  options [document = pdf, document_output = "simplewallet"]
  theories [document = false]
    "~~/src/HOL/Word/Word"
    "~~/src/HOL/Data_Structures/AVL_Map"
    "lem/Lem_bool"
    "lem/Lem_basic_classes"
    "lem/Lem_tuple"
    "lem/Lem_function"
    "lem/Lem_maybe"
    "lem/Lem_num"
    "lem/LemExtraDefs"
    "lem/Lem_set_helpers"
    "lem/Lem_map"
    "lem/Lem_string"
    "lem/Lem_word"
    "lem/Lem_show"
    "lem/Lem_sorting"
    "lem/Lem_relation"
    "lem/Lem_pervasives"
    "lem/Word256"
    "lem/Word160"
    "lem/Word8"
    "lem/Keccak"
    "lem/Evm"
	"Hoare/Hoare"
	"Hoare/HoareTripleForInstructions"
	"Hoare/HoareTripleForInstructions2"
  theories
    "example/SimpleWallet"
  document_files (in simple_wallet_document)
    "root.tex"


session "all" = "HOL" +
  theories [document = false]
    "~~/src/HOL/Word/Word"
    "~~/src/HOL/Data_Structures/AVL_Map"
    "Parse"
    ContractSem
    RelationalSem
    "Hoare/Hoare"
    "Hoare/HoareTripleForInstructions"
    "Hoare/HoareTripleForInstructions2"
    "attic/HP"
    "attic/YellowPaper"
    "example/Optimization"
    "example/AlwaysFail"
    "example/FailOnReentrance"
    "example/SimpleWallet"

session "light" = "HOL" +
  theories [document = false]
    "~~/src/HOL/Word/Word"
    "~~/src/HOL/Data_Structures/AVL_Map"
    "Hoare/HoareTripleForInstructions"
    "example/AlwaysFail"
    "example/FailOnReentrance"
    "Parse"
