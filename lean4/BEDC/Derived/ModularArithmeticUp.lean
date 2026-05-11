import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModularArithmeticUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModularArithmeticResidueCarrier [AskSetup] [PackageSetup]
    (modulus witness representative residueLedger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory modulus ∧ UnaryHistory witness ∧ UnaryHistory representative ∧
    UnaryHistory residueLedger ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
      Cont modulus witness residueLedger ∧ Cont representative residueLedger provenance ∧
        Cont provenance witness endpoint ∧ PkgSig bundle endpoint pkg

theorem ModularArithmeticResidueCarrier_stability [AskSetup] [PackageSetup]
    {modulus modulus' witness witness' representative representative' residueLedger residueLedger'
      provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueCarrier modulus witness representative residueLedger provenance
        endpoint bundle pkg ->
      hsame modulus modulus' ->
        hsame witness witness' ->
          hsame representative representative' ->
            Cont modulus' witness' residueLedger' ->
              Cont representative' residueLedger' provenance' ->
                Cont provenance' witness' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    ModularArithmeticResidueCarrier modulus' witness' representative'
                        residueLedger' provenance' endpoint' bundle pkg ∧
                      hsame residueLedger residueLedger' ∧ hsame provenance provenance' ∧
                        hsame endpoint endpoint' := by
  intro carrier sameModulus sameWitness sameRepresentative residueLedgerCont'
    provenanceCont' endpointCont' endpointPkg'
  obtain ⟨modulusUnary, witnessUnary, representativeUnary, _residueLedgerUnary,
    _provenanceUnary, _endpointUnary, residueLedgerCont, provenanceCont, endpointCont,
    _endpointPkg⟩ := carrier
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have witnessUnary' : UnaryHistory witness' :=
    unary_transport witnessUnary sameWitness
  have representativeUnary' : UnaryHistory representative' :=
    unary_transport representativeUnary sameRepresentative
  have sameResidueLedger : hsame residueLedger residueLedger' :=
    cont_respects_hsame sameModulus sameWitness residueLedgerCont residueLedgerCont'
  have residueLedgerUnary' : UnaryHistory residueLedger' :=
    unary_cont_closed modulusUnary' witnessUnary' residueLedgerCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRepresentative sameResidueLedger provenanceCont provenanceCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed representativeUnary' residueLedgerUnary' provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameWitness endpointCont endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' witnessUnary' endpointCont'
  exact
    ⟨⟨modulusUnary', witnessUnary', representativeUnary', residueLedgerUnary',
        provenanceUnary', endpointUnary', residueLedgerCont', provenanceCont', endpointCont',
        endpointPkg'⟩,
      sameResidueLedger, sameProvenance, sameEndpoint⟩

def ModularArithmeticResidueSource [AskSetup] [PackageSetup]
    (modulus witness representative residueLedger pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory modulus ∧ PositiveUnaryDenominator witness ∧ UnaryHistory representative ∧
    Cont modulus witness residueLedger ∧ Cont residueLedger representative pkgrow ∧
      PkgSig bundle pkgrow pkg

theorem ModularArithmeticResidueSource_carrier_stability [AskSetup] [PackageSetup]
    {modulus witness representative residueLedger pkgrow modulus' witness' representative'
      residueLedger' pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueSource modulus witness representative residueLedger pkgrow bundle
        pkg ->
      hsame modulus modulus' ->
        hsame witness witness' ->
          hsame representative representative' ->
            Cont modulus' witness' residueLedger' ->
              Cont residueLedger' representative' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  ModularArithmeticResidueSource modulus' witness' representative'
                      residueLedger' pkgrow' bundle pkg ∧
                    hsame residueLedger residueLedger' ∧ hsame pkgrow pkgrow' := by
  intro source sameModulus sameWitness sameRepresentative residueLedgerRow' pkgrowRow' pkgrowSig'
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport source.left sameModulus
  have witnessPositive' : PositiveUnaryDenominator witness' :=
    PositiveUnaryDenominator_hsame_transport sameWitness source.right.left
  have representativeUnary' : UnaryHistory representative' :=
    unary_transport source.right.right.left sameRepresentative
  have sameResidueLedger : hsame residueLedger residueLedger' :=
    cont_respects_hsame sameModulus sameWitness source.right.right.right.left residueLedgerRow'
  have samePkgrow : hsame pkgrow pkgrow' :=
    cont_respects_hsame sameResidueLedger sameRepresentative
      source.right.right.right.right.left pkgrowRow'
  exact And.intro
    (And.intro modulusUnary'
      (And.intro witnessPositive'
        (And.intro representativeUnary'
          (And.intro residueLedgerRow' (And.intro pkgrowRow' pkgrowSig')))))
    (And.intro sameResidueLedger samePkgrow)

theorem ModularArithmeticResidueSource_add_mul_ledger [AskSetup] [PackageSetup]
    {modulus witness left right addRow mulRow addLedger mulLedger addPkg mulPkg : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueSource modulus witness left addLedger addPkg bundle pkg ->
      ModularArithmeticResidueSource modulus witness right mulLedger mulPkg bundle pkg ->
        Cont left right addRow ->
          Cont left right mulRow ->
            UnaryHistory addRow ∧ UnaryHistory mulRow ∧ hsame addRow (append left right) ∧
              hsame mulRow (append left right) ∧ PkgSig bundle addPkg pkg ∧
                PkgSig bundle mulPkg pkg := by
  intro leftSource rightSource addCont mulCont
  have leftUnary : UnaryHistory left :=
    leftSource.right.right.left
  have rightUnary : UnaryHistory right :=
    rightSource.right.right.left
  have addUnary : UnaryHistory addRow :=
    unary_cont_closed leftUnary rightUnary addCont
  have mulUnary : UnaryHistory mulRow :=
    unary_cont_closed leftUnary rightUnary mulCont
  have addSame : hsame addRow (append left right) :=
    addCont
  have mulSame : hsame mulRow (append left right) :=
    mulCont
  have addPkgSig : PkgSig bundle addPkg pkg :=
    leftSource.right.right.right.right.right
  have mulPkgSig : PkgSig bundle mulPkg pkg :=
    rightSource.right.right.right.right.right
  exact And.intro addUnary
    (And.intro mulUnary
      (And.intro addSame
        (And.intro mulSame
          (And.intro addPkgSig mulPkgSig))))

theorem ModularArithmeticResidueSource_int_rat_handoff [AskSetup] [PackageSetup]
    {modulus witness representative residueLedger pkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueSource modulus witness representative residueLedger pkgrow bundle
        pkg ->
      UnaryHistory modulus ∧ PositiveUnaryDenominator witness ∧ UnaryHistory witness ∧
        UnaryHistory representative ∧ Cont modulus witness residueLedger ∧
          Cont residueLedger representative pkgrow ∧ hsame residueLedger (append modulus witness) ∧
            hsame pkgrow (append residueLedger representative) ∧ PkgSig bundle pkgrow pkg := by
  intro source
  have witnessRows := PositiveUnaryDenominator_unary_and_nonempty source.right.left
  exact And.intro source.left
    (And.intro source.right.left
      (And.intro witnessRows.left
        (And.intro source.right.right.left
          (And.intro source.right.right.right.left
            (And.intro source.right.right.right.right.left
              (And.intro source.right.right.right.left
                (And.intro source.right.right.right.right.left
                  source.right.right.right.right.right)))))))

theorem ModularArithmeticResidueSource_scoped_dependency_boundary [AskSetup] [PackageSetup]
    {modulus witness representative residueLedger pkgrow modulus' witness' representative'
      residueLedger' pkgrow' endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModularArithmeticResidueSource modulus witness representative residueLedger pkgrow bundle
        pkg ->
      hsame modulus modulus' ->
        hsame witness witness' ->
          hsame representative representative' ->
            Cont modulus' witness' residueLedger' ->
              Cont residueLedger' representative' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  Cont pkgrow' witness' endpoint ->
                    ModularArithmeticResidueSource modulus' witness' representative'
                        residueLedger' pkgrow' bundle pkg ∧
                      PositiveUnaryDenominator witness' ∧ UnaryHistory witness' ∧
                        hsame residueLedger residueLedger' ∧ hsame pkgrow pkgrow' ∧
                          hsame endpoint (append pkgrow' witness') := by
  intro source sameModulus sameWitness sameRepresentative residueLedgerRow' pkgrowRow'
    pkgrowSig' endpointRow
  have stable :=
    ModularArithmeticResidueSource_carrier_stability source sameModulus sameWitness
      sameRepresentative residueLedgerRow' pkgrowRow' pkgrowSig'
  have witnessPositive : PositiveUnaryDenominator witness' :=
    stable.left.right.left
  have witnessUnary : UnaryHistory witness' :=
    (PositiveUnaryDenominator_unary_and_nonempty witnessPositive).left
  exact
    And.intro stable.left
      (And.intro witnessPositive
        (And.intro witnessUnary
          (And.intro stable.right.left (And.intro stable.right.right endpointRow))))

end BEDC.Derived.ModularArithmeticUp
