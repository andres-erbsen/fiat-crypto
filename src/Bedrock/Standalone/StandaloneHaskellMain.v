From Coq Require Import List.
From Coq Require Import String.
Require Import Crypto.CLI.
Require Export Crypto.StandaloneHaskellMain.
Require Import Crypto.Bedrock.Field.Stringification.Stringification.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Module Bedrock2First.
  (** N.B. We put bedrock2 first so that the default for these binaries
      is bedrock2 *)
  Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
    := [("bedrock2", OutputBedrock2API)]
         ++ ForExtraction.default_supported_languages.

  Module UnsaturatedSolinas.
    Definition main : IO_unit
      := main_gen ForExtraction.UnsaturatedSolinas.PipelineMain.
  End UnsaturatedSolinas.

  Module WordByWordMontgomery.
    Definition main : IO_unit
      := main_gen ForExtraction.WordByWordMontgomery.PipelineMain.
  End WordByWordMontgomery.

  Module DettmanMultiplication.
    Definition main : IO_unit
      := main_gen ForExtraction.DettmanMultiplication.PipelineMain.
  End DettmanMultiplication.

  Module P256ADX.
    Definition main : IO_unit
      := main_gen ForExtraction.P256ADX.PipelineMain.
  End P256ADX.

  Module BaseConversion.
    Definition main : IO_unit
      := main_gen ForExtraction.BaseConversion.PipelineMain.
  End BaseConversion.

  Module FiatCrypto.
    Definition main : IO_unit
      := main_gen ForExtraction.FiatCrypto.PipelineMain.
  End FiatCrypto.
End Bedrock2First.

Module Bedrock2Later.
  Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
    := let bedrock2 := ("bedrock2", OutputBedrock2API) in
       match ForExtraction.default_supported_languages with
       | l :: ls => l :: bedrock2 :: ls
       | ls => bedrock2 :: ls
       end.

  Module UnsaturatedSolinas.
    Definition main : IO_unit
      := main_gen ForExtraction.UnsaturatedSolinas.PipelineMain.
  End UnsaturatedSolinas.

  Module WordByWordMontgomery.
    Definition main : IO_unit
      := main_gen ForExtraction.WordByWordMontgomery.PipelineMain.
  End WordByWordMontgomery.

  Module DettmanMultiplication.
    Definition main : IO_unit
      := main_gen ForExtraction.DettmanMultiplication.PipelineMain.
  End DettmanMultiplication.

  Module P256ADX.
    Definition main : IO_unit
      := main_gen ForExtraction.P256ADX.PipelineMain.
  End P256ADX.

  Module BaseConversion.
    Definition main : IO_unit
      := main_gen ForExtraction.BaseConversion.PipelineMain.
  End BaseConversion.

  Module FiatCrypto.
    Definition main : IO_unit
      := main_gen ForExtraction.FiatCrypto.PipelineMain.
  End FiatCrypto.
End Bedrock2Later.
