import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorLedgerDescent
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      sigRead motiveRead branchRead descentRead outputRead auditRead : BHist} :
    Cont signature eliminator sigRead ->
      Cont sigRead motive motiveRead ->
        Cont motiveRead branches branchRead ->
          Cont branchRead descent descentRead ->
            Cont descentRead output outputRead ->
              Cont outputRead audit auditRead ->
                UnaryHistory signature ->
                  UnaryHistory eliminator ->
                    UnaryHistory motive ->
                      UnaryHistory branches ->
                        UnaryHistory descent ->
                          UnaryHistory output ->
                            UnaryHistory audit ->
                              authorizedGeneratorRecursorFromEventFlow
                                  (authorizedGeneratorRecursorToEventFlow
                                    (AuthorizedGeneratorRecursorUp.mk signature eliminator
                                      motive branches descent output audit transport routes
                                      provenance gap name)) =
                                some
                                  (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                    branches descent output audit transport routes provenance gap
                                    name) ∧
                                UnaryHistory sigRead ∧ UnaryHistory motiveRead ∧
                                  UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                                    UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                                      Cont signature eliminator sigRead ∧
                                        Cont sigRead motive motiveRead ∧
                                          Cont motiveRead branches branchRead ∧
                                            Cont branchRead descent descentRead ∧
                                              Cont descentRead output outputRead ∧
                                                Cont outputRead audit auditRead ∧
                                                  authorizedGeneratorRecursorEncodeBHist
                                                      BHist.Empty =
                                                    ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro signatureEliminatorSigRead sigReadMotiveRead motiveReadBranchesBranchRead
    branchReadDescentRead descentReadOutputRead outputReadAuditRead signatureUnary
    eliminatorUnary motiveUnary branchesUnary descentUnary outputUnary auditUnary
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
            audit transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have sigReadUnary : UnaryHistory sigRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorSigRead
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed sigReadUnary motiveUnary sigReadMotiveRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary branchesUnary motiveReadBranchesBranchRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary descentUnary branchReadDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentReadOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary outputReadAuditRead
  exact
    ⟨roundTrip, sigReadUnary, motiveReadUnary, branchReadUnary, descentReadUnary,
      outputReadUnary, auditReadUnary, signatureEliminatorSigRead, sigReadMotiveRead,
      motiveReadBranchesBranchRead, branchReadDescentRead, descentReadOutputRead,
      outputReadAuditRead, rfl⟩

theorem AuthorizedGeneratorRecursorConsumerNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance boundary
      nameCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : AuthorizedGeneratorRecursorUp,
        packet =
          AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance boundary nameCert) ->
      Cont signature eliminator motive ->
        Cont motive branches descent ->
          Cont descent output audit ->
            Cont audit nameCert consumerRead ->
              PkgSig bundle provenance pkg ->
                PkgSig bundle consumerRead pkg ->
                  hsame consumerRead (append audit nameCert) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                      Cont audit nameCert consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro packetWitness _signatureEliminator _motiveBranches _descentOutput auditName
    provenancePkg consumerPkg
  obtain ⟨_packet, packetEq⟩ := packetWitness
  cases packetEq
  exact ⟨auditName, provenancePkg, consumerPkg, auditName⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
