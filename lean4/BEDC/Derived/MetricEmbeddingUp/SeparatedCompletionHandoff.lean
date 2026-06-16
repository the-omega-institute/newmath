import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricEmbeddingCarrier_separated_completion_handoff [AskSetup] [PackageSetup]
    {X Y F D R S H C P N graphRead controlRead sealedRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X F graphRead →
      Cont graphRead D controlRead →
        Cont controlRead R sealedRead →
          Cont sealedRead S separatedRead →
            UnaryHistory X →
              UnaryHistory F →
                UnaryHistory D →
                  UnaryHistory R →
                    UnaryHistory S →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row F ∨ hsame row D ∨ hsame row R ∨
                                  hsame row S ∨ hsame row separatedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont X F graphRead ∧
                                  Cont graphRead D controlRead ∧
                                    Cont controlRead R sealedRead ∧
                                      Cont sealedRead S separatedRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory graphRead ∧ UnaryHistory controlRead ∧
                              UnaryHistory sealedRead ∧ UnaryHistory separatedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory PkgSig
  intro graphRoute controlRoute sealedRoute separatedRoute xUnary fUnary dUnary rUnary sUnary
    provenancePkg namePkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed xUnary fUnary graphRoute
  have controlUnary : UnaryHistory controlRead :=
    unary_cont_closed graphUnary dUnary controlRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed controlUnary rUnary sealedRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed sealedUnary sUnary separatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row D ∨ hsame row R ∨
              hsame row S ∨ hsame row separatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F graphRead ∧ Cont graphRead D controlRead ∧
              Cont controlRead R sealedRead ∧ Cont sealedRead S separatedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separatedRead ⟨hsame_refl separatedRead, separatedUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, controlRoute, sealedRoute, separatedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, graphUnary, controlUnary, sealedUnary, separatedUnary⟩

end BEDC.Derived.MetricEmbeddingUp
