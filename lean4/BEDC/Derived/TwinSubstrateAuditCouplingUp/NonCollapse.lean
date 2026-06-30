import BEDC.Derived.TwinSubstrateAuditCouplingUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.TwinSubstrateAuditCouplingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TwinSubstrateAuditCouplingCarrier_noncollapse [AskSetup] [PackageSetup]
    {M G R L C H T P N metaRoute groundRoute pairedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ∧ UnaryHistory G ∧ UnaryHistory R ∧ UnaryHistory L ∧
      UnaryHistory C ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg →
      Cont M R metaRoute →
        Cont G R groundRoute →
          Cont metaRoute L pairedRead →
            Cont groundRoute C pairedRead →
              PkgSig bundle pairedRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row M ∨ hsame row G ∨ hsame row pairedRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row G ∨ hsame row R ∨ hsame row L ∨
                        hsame row C ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                          hsame row N ∨ hsame row pairedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M R metaRoute ∧
                        Cont G R groundRoute ∧ PkgSig bundle pairedRead pkg)
                    hsame ∧
                  UnaryHistory metaRoute ∧ UnaryHistory groundRoute ∧
                    UnaryHistory pairedRead := by
  -- BEDC touchpoint anchor: TwinSubstrateAuditCouplingUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metaRouteCont groundRouteCont pairedFromMeta _pairedFromGround pairedPkg
  obtain ⟨mUnary, gUnary, rUnary, lUnary, _cUnary, _hUnary, _tUnary, _pUnary,
    _nUnary, _pPkg, _nPkg⟩ := carrier
  have metaRouteUnary : UnaryHistory metaRoute :=
    unary_cont_closed mUnary rUnary metaRouteCont
  have groundRouteUnary : UnaryHistory groundRoute :=
    unary_cont_closed gUnary rUnary groundRouteCont
  have pairedUnary : UnaryHistory pairedRead :=
    unary_cont_closed metaRouteUnary lUnary pairedFromMeta
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row M ∨ hsame row G ∨ hsame row pairedRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row R ∨ hsame row L ∨ hsame row C ∨
              hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N ∨
                hsame row pairedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R metaRoute ∧ Cont G R groundRoute ∧
              PkgSig bundle pairedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro pairedRead
          ⟨Or.inr (Or.inr (hsame_refl pairedRead)), pairedUnary⟩
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
          | inl sameM =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameM)
          | inr rest =>
              cases rest with
              | inl sameG =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameG))
              | inr samePaired =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) samePaired))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameM =>
          exact Or.inl sameM
      | inr rest =>
          cases rest with
          | inl sameG =>
              exact Or.inr (Or.inl sameG)
          | inr samePaired =>
              right
              right
              right
              right
              right
              right
              right
              right
              right
              exact samePaired
    ledger_sound := by
      intro _row source
      exact ⟨source.right, metaRouteCont, groundRouteCont, pairedPkg⟩
  }
  exact ⟨cert, metaRouteUnary, groundRouteUnary, pairedUnary⟩

end BEDC.Derived.TwinSubstrateAuditCouplingUp
