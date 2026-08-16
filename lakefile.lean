import Lake

open Lake DSL

package opencsv

@[default_target]
lean_lib OpenCsv

lean_exe «gen-model-corpus» where
  root := `OpenCsv.Corpus
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-fuse-ld=/usr/bin/ld", "-Wl,-no_data_const"]
    else
      #[]
