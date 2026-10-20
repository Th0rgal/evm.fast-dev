import InitECandidate.Proofs.CompilerConfigLiteral
import InitECandidate.Proofs.CompilerOracles
import InitECandidate.Proofs.WordBackend.FunctionsFacts

namespace InitE
open InitECandidate.Proofs

/-- Baseline compilation uses the fixed, compiler-validated allocation tape. -/
def baselineCompilerConfig : Flapjack.Compiler.Backend.Backend.Config :=
  oracleCompilerConfig WordBackend.oracles

/-- The literal output metadata with the checked input allocation configuration. -/
def baselineConfigLiteralWithOracles : Flapjack.Compiler.Backend.Backend.Config :=
  { baselineConfigLiteral with wordToWordConf := baselineCompilerConfig.wordToWordConf }

/-- Certified literal metadata, so installation facts do not recompile the guest. -/
def baselineConfig : Flapjack.Compiler.Backend.Backend.Config := baselineConfigLiteralWithOracles

end InitE
