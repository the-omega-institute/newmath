import BEDC.Derived.BoundedSetUp.RadiusLedger

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_real_radius_ledger [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow radiusRead ledgerRead orderRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont center radius radiusRead ->
        Cont radiusRead ball ledgerRead ->
          Cont ledgerRead transport orderRead ->
            PkgSig bundle ledgerRead pkg ->
              PkgSig bundle orderRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row radius ∨ hsame row ball ∨ hsame row ledgerRead ∨
                        Cont ledgerRead transport orderRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
                        PkgSig bundle orderRead pkg ∧ hsame row orderRead)
                    hsame ∧
                  UnaryHistory radius ∧ UnaryHistory radiusRead ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory orderRead ∧ Cont center radius radiusRead ∧
                      Cont radiusRead ball ledgerRead ∧ Cont ledgerRead transport orderRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier centerRadius radiusBallLedger ledgerTransportOrder ledgerPkg orderPkg
  obtain ⟨_xUnary, _sUnary, centerUnary, radiusUnary, ballUnary, transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centerUnary radiusUnary centerRadius
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed radiusReadUnary ballUnary radiusBallLedger
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed ledgerReadUnary transportUnary ledgerTransportOrder
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row radius ∨ hsame row ball ∨ hsame row ledgerRead ∨
              Cont ledgerRead transport orderRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg ∧
              PkgSig bundle orderRead pkg ∧ hsame row orderRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro orderRead ⟨hsame_refl orderRead, orderReadUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr ledgerTransportOrder))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, ledgerPkg, orderPkg, source.left⟩
  }
  exact
    ⟨cert, radiusUnary, radiusReadUnary, ledgerReadUnary, orderReadUnary, centerRadius,
      radiusBallLedger, ledgerTransportOrder⟩

end BEDC.Derived.BoundedSetUp
