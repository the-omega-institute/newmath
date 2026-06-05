import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

inductive FiniteOscillationUniformModulusUp : Type where
  | mk (K M A B O U H C P N : BHist) : FiniteOscillationUniformModulusUp

def finiteOscillationUniformModulusFields :
    FiniteOscillationUniformModulusUp → List BHist
  | FiniteOscillationUniformModulusUp.mk K M A B O U H C P N =>
      [K, M, A, B, O, U, H, C, P, N]

theorem FiniteOscillationUniformModulusNameCertObligations [AskSetup] [PackageSetup]
    {K M A B O U H C P N compactRead continuityRead partitionRead oscillationRead
      uniformRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
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
                      Cont K M compactRead →
                        Cont compactRead A continuityRead →
                          Cont continuityRead B partitionRead →
                            Cont partitionRead O oscillationRead →
                              Cont oscillationRead U uniformRead →
                                Cont uniformRead C replayRead →
                                  Cont replayRead N namedRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row K ∨ hsame row M ∨ hsame row A ∨
                                                hsame row B ∨ hsame row O ∨ hsame row U ∨
                                                  hsame row namedRead ∨
                                                    Cont replayRead N namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont K M compactRead ∧
                                                Cont compactRead A continuityRead ∧
                                                  Cont continuityRead B partitionRead ∧
                                                    Cont partitionRead O oscillationRead ∧
                                                      Cont oscillationRead U uniformRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldsEq unaryK unaryM unaryA unaryB unaryO unaryU unaryC unaryN compactRoute
    continuityRoute partitionRoute oscillationRoute uniformRoute replayRoute namedRoute
    pkgP pkgN
  have _packetRows :
      finiteOscillationUniformModulusFields
          (FiniteOscillationUniformModulusUp.mk K M A B O U H C P N) =
            [K, M, A, B, O, U, H, C, P, N] :=
    fieldsEq
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryM compactRoute
  have continuityReadUnary : UnaryHistory continuityRead :=
    unary_cont_closed compactReadUnary unaryA continuityRoute
  have partitionReadUnary : UnaryHistory partitionRead :=
    unary_cont_closed continuityReadUnary unaryB partitionRoute
  have oscillationReadUnary : UnaryHistory oscillationRead :=
    unary_cont_closed partitionReadUnary unaryO oscillationRoute
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed oscillationReadUnary unaryU uniformRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed uniformReadUnary unaryC replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row M ∨ hsame row A ∨ hsame row B ∨ hsame row O ∨
              hsame row U ∨ hsame row namedRead ∨ Cont replayRead N namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K M compactRead ∧
              Cont compactRead A continuityRead ∧ Cont continuityRead B partitionRead ∧
                Cont partitionRead O oscillationRead ∧ Cont oscillationRead U uniformRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, continuityRoute, partitionRoute, oscillationRoute,
          uniformRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, namedReadUnary⟩

end BEDC.Derived.FiniteOscillationUniformModulusUp
