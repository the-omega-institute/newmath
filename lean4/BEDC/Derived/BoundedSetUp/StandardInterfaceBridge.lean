import BEDC.Derived.BoundedSetUp.BallContainmentRoute
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_standard_interface_bridge [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      consumerRead bornology ledgerRead standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead replay consumerRead ->
            Cont ball transport bornology ->
              Cont ball replay ledgerRead ->
                Cont bornology ledgerRead standardRead ->
                  PkgSig bundle consumerRead pkg ->
                    PkgSig bundle bornology pkg ->
                      PkgSig bundle ledgerRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row X ∨ hsame row S ∨ hsame row center ∨
                                hsame row radius ∨ hsame row ball ∨ hsame row bornology ∨
                                  hsame row ledgerRead ∨ Cont bornology ledgerRead standardRead)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                                PkgSig bundle bornology pkg ∧ PkgSig bundle ledgerRead pkg ∧
                                  hsame row standardRead)
                            hsame ∧
                          UnaryHistory standardRead ∧ Cont bornology ledgerRead standardRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier subsetCenter memberRadius ballReplayConsumer ballTransportBornology
    ballReplayLedger bornologyLedgerStandard consumerPkg bornologyPkg ledgerPkg
  obtain ⟨_xUnary, _sUnary, _centerUnary, _radiusUnary, ballUnary, transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have bornologyUnary : UnaryHistory bornology :=
    unary_cont_closed ballUnary transportUnary ballTransportBornology
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ballUnary replayUnary ballReplayLedger
  have standardUnary : UnaryHistory standardRead :=
    unary_cont_closed bornologyUnary ledgerUnary bornologyLedgerStandard
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
              hsame row ball ∨ hsame row bornology ∨ hsame row ledgerRead ∨
                Cont bornology ledgerRead standardRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              PkgSig bundle bornology pkg ∧ PkgSig bundle ledgerRead pkg ∧
                hsame row standardRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro standardRead
        ⟨hsame_refl standardRead, standardUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr bornologyLedgerStandard))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, bornologyPkg, ledgerPkg, source.left⟩
  }
  exact ⟨cert, standardUnary, bornologyLedgerStandard⟩

end BEDC.Derived.BoundedSetUp
