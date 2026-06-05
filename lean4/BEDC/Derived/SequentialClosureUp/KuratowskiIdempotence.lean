import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureKuratowskiIdempotence [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N firstLimit firstWindow firstSeal named secondLimit
      secondWindow secondSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg →
      Cont L U firstLimit →
        Cont firstLimit W firstWindow →
          Cont firstWindow A firstSeal →
            Cont firstSeal N named →
              Cont named U secondLimit →
                Cont secondLimit W secondWindow →
                  Cont secondWindow A secondSeal →
                    PkgSig bundle named pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row secondSeal ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row A ∨
                              hsame row named ∨ hsame row secondSeal)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont named U secondLimit ∧
                              Cont secondLimit W secondWindow ∧
                                Cont secondWindow A secondSeal ∧ PkgSig bundle named pkg)
                          hsame ∧
                        UnaryHistory secondLimit ∧ UnaryHistory secondWindow ∧
                          UnaryHistory secondSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier firstLimitRoute firstWindowRoute firstSealRoute namedRoute
    secondLimitRoute secondWindowRoute secondSealRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, _sourceUnary, _sequenceUnary, limitUnaryBase,
    testUnary, windowUnaryBase, _regSeqUnary, sealUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nameUnary, _provenancePkg, _localNamePkg⟩ :=
    carrier
  have firstLimitUnary : UnaryHistory firstLimit :=
    unary_cont_closed limitUnaryBase testUnary firstLimitRoute
  have firstWindowUnary : UnaryHistory firstWindow :=
    unary_cont_closed firstLimitUnary windowUnaryBase firstWindowRoute
  have firstSealUnary : UnaryHistory firstSeal :=
    unary_cont_closed firstWindowUnary sealUnaryBase firstSealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed firstSealUnary nameUnary namedRoute
  have secondLimitUnary : UnaryHistory secondLimit :=
    unary_cont_closed namedUnary testUnary secondLimitRoute
  have secondWindowUnary : UnaryHistory secondWindow :=
    unary_cont_closed secondLimitUnary windowUnaryBase secondWindowRoute
  have secondSealUnary : UnaryHistory secondSeal :=
    unary_cont_closed secondWindowUnary sealUnaryBase secondSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row secondSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row A ∨
              hsame row named ∨ hsame row secondSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont named U secondLimit ∧
              Cont secondLimit W secondWindow ∧ Cont secondWindow A secondSeal ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro secondSeal ⟨hsame_refl secondSeal, secondSealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, secondLimitRoute, secondWindowRoute, secondSealRoute, namedPkg⟩
  }
  exact ⟨cert, secondLimitUnary, secondWindowUnary, secondSealUnary⟩

end BEDC.Derived.SequentialClosureUp
