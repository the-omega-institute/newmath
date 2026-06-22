import BEDC.Derived.BooleanalgebraUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BooleanalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BooleanAlgebraPublicNameCertExport [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName regularRead
      stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont join meet regularRead →
        Cont order localName stoneRead →
          PkgSig bundle regularRead pkg →
            PkgSig bundle stoneRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row regularRead ∨ hsame row stoneRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                      hsame row one ∨ hsame row order ∨ hsame row regularRead ∨
                        hsame row stoneRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont join meet regularRead ∧
                      Cont order localName stoneRead ∧ PkgSig bundle regularRead pkg ∧
                        PkgSig bundle stoneRead pkg)
                  hsame ∧
                UnaryHistory regularRead ∧ UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows regularRoute stoneRoute regularPkg stonePkg
  obtain ⟨joinUnary, meetUnary, _complUnary, _zeroUnary, _oneUnary, orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ :=
      carrierRows
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed joinUnary meetUnary regularRoute
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed orderUnary localNameUnary stoneRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row regularRead ∨ hsame row stoneRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row regularRead ∨
                hsame row stoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont join meet regularRead ∧
              Cont order localName stoneRead ∧ PkgSig bundle regularRead pkg ∧
                PkgSig bundle stoneRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regularRead ⟨Or.inl (hsame_refl regularRead), regularUnary⟩
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
          | inl regularSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) regularSame)
          | inr stoneSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) stoneSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl regularSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl regularSame))))))
      | inr stoneSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr stoneSame))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularRoute, stoneRoute, regularPkg, stonePkg⟩
  }
  exact ⟨cert, regularUnary, stoneUnary⟩

end BEDC.Derived.BooleanalgebraUp
