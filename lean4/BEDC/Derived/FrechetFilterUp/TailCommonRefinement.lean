import BEDC.Derived.FrechetFilterUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterTailCommonRefinement [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N U2 T2 commonTail leftRead rightRead
      meetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      UnaryHistory U2 ->
        UnaryHistory T2 ->
          Cont U T leftRead ->
            Cont U2 T2 rightRead ->
              Cont leftRead rightRead commonTail ->
                Cont commonTail B meetRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row commonTail ∨ hsame row meetRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row U ∨ hsame row T ∨ hsame row U2 ∨
                              hsame row T2 ∨ hsame row B ∨ hsame row commonTail ∨
                                hsame row meetRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont U T leftRead ∧
                              Cont U2 T2 rightRead ∧ Cont leftRead rightRead commonTail ∧
                                Cont commonTail B meetRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory commonTail ∧ UnaryHistory meetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier u2Unary t2Unary leftRoute rightRoute commonRoute meetRoute provenancePkg
    namePkg
  obtain ⟨uUnary, tUnary, _sUnary, _mUnary, bUnary, _qUnary, _rUnary, _aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierTail, _carrierSchedule,
    _carrierFilter, _carrierSeal, _carrierProvenance, _carrierName⟩ := carrier
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed uUnary tUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed u2Unary t2Unary rightRoute
  have commonUnary : UnaryHistory commonTail :=
    unary_cont_closed leftUnary rightUnary commonRoute
  have meetUnary : UnaryHistory meetRead :=
    unary_cont_closed commonUnary bUnary meetRoute
  have sourceCommon :
      (fun row : BHist =>
        (hsame row commonTail ∨ hsame row meetRead) ∧ UnaryHistory row) commonTail := by
    exact ⟨Or.inl (hsame_refl commonTail), commonUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row commonTail ∨ hsame row meetRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row T ∨ hsame row U2 ∨ hsame row T2 ∨ hsame row B ∨
              hsame row commonTail ∨ hsame row meetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U T leftRead ∧ Cont U2 T2 rightRead ∧
              Cont leftRead rightRead commonTail ∧ Cont commonTail B meetRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro commonTail sourceCommon
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
        constructor
        · cases source.left with
          | inl commonSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) commonSame)
          | inr meetSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) meetSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl commonSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl commonSame)))))
      | inr meetSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr meetSame)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftRoute, rightRoute, commonRoute, meetRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, commonUnary, meetUnary⟩

end BEDC.Derived.FrechetFilterUp
