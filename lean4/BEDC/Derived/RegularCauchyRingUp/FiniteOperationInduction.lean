import BEDC.Derived.RegularCauchyRingUp

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRingCarrier_finite_operation_induction [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N sumRead negRead
      productRead scaleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont S ES sumRead →
        Cont G EG negRead →
          Cont M EM productRead →
            Cont L EL scaleRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row sumRead ∨ hsame row negRead ∨ hsame row productRead ∨
                            hsame row scaleRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row G ∨ hsame row M ∨ hsame row L ∨
                          hsame row sumRead ∨ hsame row negRead ∨ hsame row productRead ∨
                            hsame row scaleRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S ES sumRead ∧ Cont G EG negRead ∧
                          Cont M EM productRead ∧ Cont L EL scaleRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory sumRead ∧ UnaryHistory negRead ∧ UnaryHistory productRead ∧
                      UnaryHistory scaleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sumRoute negRoute productRoute scaleRoute provenancePkg namePkg
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, _daUnary, _dbUnary, sUnary, gUnary,
    mUnary, lUnary, _rsUnary, _rgUnary, _rmUnary, _rlUnary, esUnary, egUnary, emUnary,
    elUnary, _hUnary, _cUnary, _pUnary, _nUnary, _sourceWindowA, _sourceWindowB,
    _transportReplay, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed sUnary esUnary sumRoute
  have negUnary : UnaryHistory negRead :=
    unary_cont_closed gUnary egUnary negRoute
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed mUnary emUnary productRoute
  have scaleUnary : UnaryHistory scaleRead :=
    unary_cont_closed lUnary elUnary scaleRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sumRead ∨ hsame row negRead ∨ hsame row productRead ∨
                hsame row scaleRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row G ∨ hsame row M ∨ hsame row L ∨
              hsame row sumRead ∨ hsame row negRead ∨ hsame row productRead ∨
                hsame row scaleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S ES sumRead ∧ Cont G EG negRead ∧
              Cont M EM productRead ∧ Cont L EL scaleRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sumRead ⟨Or.inl (hsame_refl sumRead), sumUnary⟩
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
            | inl sameSum =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameSum)
            | inr rest =>
                cases rest with
                | inl sameNeg =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNeg))
                | inr rest =>
                    cases rest with
                    | inl sameProduct =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameProduct)))
                    | inr sameScale =>
                        exact Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameScale)))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameSum =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSum))))
        | inr rest =>
            cases rest with
            | inl sameNeg =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameNeg)))))
            | inr rest =>
                cases rest with
                | inl sameProduct =>
                    exact Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameProduct))))))
                | inr sameScale =>
                    exact Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameScale))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, sumRoute, negRoute, productRoute, scaleRoute, provenancePkg, namePkg⟩
    }
  exact ⟨cert, sumUnary, negUnary, productUnary, scaleUnary⟩

end BEDC.Derived.RegularCauchyRingUp
