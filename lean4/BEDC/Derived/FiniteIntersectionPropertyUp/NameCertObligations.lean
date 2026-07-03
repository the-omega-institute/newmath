import BEDC.Derived.FiniteIntersectionPropertyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteIntersectionPropertyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteIntersectionPropertyNameCertObligations [AskSetup] [PackageSetup]
    {J F A Q N C E R H T P M witness sealed replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory F →
        UnaryHistory A →
          UnaryHistory Q →
            UnaryHistory N →
              UnaryHistory C →
                UnaryHistory E →
                  UnaryHistory R →
                    UnaryHistory H →
                      UnaryHistory T →
                        UnaryHistory P →
                          UnaryHistory M →
                            Cont J F A →
                              Cont A Q witness →
                                Cont witness R sealed →
                                  Cont sealed T replay →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle M pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row sealed ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row J ∨ hsame row F ∨
                                                hsame row A ∨ hsame row Q ∨
                                                  hsame row N ∨ hsame row C ∨
                                                    hsame row E ∨ hsame row R ∨
                                                      hsame row H ∨ hsame row T ∨
                                                        hsame row P ∨ hsame row M ∨
                                                          hsame row witness ∨
                                                            hsame row sealed)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont J F A ∧
                                                Cont A Q witness ∧
                                                  Cont witness R sealed ∧
                                                    Cont sealed T replay ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle M pkg)
                                            hsame ∧
                                          UnaryHistory witness ∧ UnaryHistory sealed ∧
                                            UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro jUnary _fUnary aUnary qUnary _nUnary _cUnary _eUnary rUnary _hUnary tUnary
    _pUnary _mUnary rootRoute witnessRoute sealRoute replayRoute provenancePkg namePkg
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed aUnary qUnary witnessRoute
  have sealUnary : UnaryHistory sealed :=
    unary_cont_closed witnessUnary rUnary sealRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed sealUnary tUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealed ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row F ∨ hsame row A ∨ hsame row Q ∨
              hsame row N ∨ hsame row C ∨ hsame row E ∨ hsame row R ∨
                hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row M ∨
                  hsame row witness ∨ hsame row sealed)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J F A ∧ Cont A Q witness ∧
              Cont witness R sealed ∧ Cont sealed T replay ∧ PkgSig bundle P pkg ∧
                PkgSig bundle M pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨sealed, hsame_refl sealed, sealUnary⟩
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
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, rootRoute, witnessRoute, sealRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, witnessUnary, sealUnary, replayUnary⟩

end BEDC.Derived.FiniteIntersectionPropertyUp
