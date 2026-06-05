import BEDC.Derived.FiniteOscillationUniformModulusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteOscillationUniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteOscillationUniformModulusCarrier_namecert_obligations [AskSetup]
    [PackageSetup] {K M A B O U H C P N partitionRead oscillationRead uniformRead
      replayRead namedRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteOscillationUniformModulusFields
        (FiniteOscillationUniformModulusUp.mk K M A B O U H C P N) =
        [K, M, A, B, O, U, H, C, P, N] →
      UnaryHistory K →
        UnaryHistory M →
          UnaryHistory A →
            UnaryHistory B →
              UnaryHistory O →
                UnaryHistory U →
                  UnaryHistory C →
                    UnaryHistory N →
                      Cont K M partitionRead →
                        Cont partitionRead A oscillationRead →
                          Cont oscillationRead B uniformRead →
                            Cont uniformRead C replayRead →
                              Cont replayRead N namedRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row uniformRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row K ∨ hsame row B ∨ hsame row O ∨
                                            hsame row U ∨ hsame row namedRead ∨
                                              Cont oscillationRead B uniformRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont K M partitionRead ∧
                                              Cont partitionRead A oscillationRead ∧
                                                Cont oscillationRead B uniformRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory uniformRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro hfields unaryK unaryM unaryA unaryB unaryO unaryU unaryC unaryN routeKM
    routePartition routeOscillation routeReplay routeNamed provenancePkg localNamePkg
  cases hfields
  have partitionUnary : UnaryHistory partitionRead :=
    unary_cont_closed unaryK unaryM routeKM
  have oscillationUnary : UnaryHistory oscillationRead :=
    unary_cont_closed partitionUnary unaryA routePartition
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed oscillationUnary unaryB routeOscillation
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed uniformUnary unaryC routeReplay
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary unaryN routeNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row O ∨ hsame row U ∨
              hsame row namedRead ∨ Cont oscillationRead B uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K M partitionRead ∧
              Cont partitionRead A oscillationRead ∧
                Cont oscillationRead B uniformRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr routeOscillation))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeKM, routePartition, routeOscillation, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, uniformUnary, namedUnary⟩

end BEDC.Derived.FiniteOscillationUniformModulusUp
