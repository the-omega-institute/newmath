import BEDC.Derived.GroupUp
import BEDC.Derived.ModuleUp
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CharacterTheoryUp

open BEDC.Derived.GroupUp
open BEDC.Derived.ModuleUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CharacterTheoryRootCarrier_obligation [AskSetup] [PackageSetup]
    {group vector action trace ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GroupSingletonCarrier group ->
      VecSpaceSingletonCarrier vector ->
        Cont group vector action ->
          Cont action BHist.Empty trace ->
            PkgSig bundle ledger pkg ->
              GroupSingletonCarrier group ∧ VecSpaceSingletonCarrier vector ∧
                hsame action BHist.Empty ∧ hsame trace BHist.Empty ∧
                  PkgSig bundle ledger pkg := by
  intro groupCarrier vectorCarrier actionCont traceCont pkgSig
  have actionEmpty : hsame action BHist.Empty := by
    exact actionCont.trans (append_eq_empty_iff.mpr (And.intro groupCarrier vectorCarrier))
  have traceAction : hsame trace action :=
    cont_right_unit_result traceCont
  have traceEmpty : hsame trace BHist.Empty :=
    hsame_trans traceAction actionEmpty
  exact And.intro groupCarrier
    (And.intro vectorCarrier
      (And.intro actionEmpty
        (And.intro traceEmpty pkgSig)))

def CharacterTheoryRootBHistSurface [AskSetup] [PackageSetup]
    (group vector action trace orthLedger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory group ∧ UnaryHistory vector ∧ Cont group vector action ∧
    UnaryHistory trace ∧ Cont action trace orthLedger ∧ Cont orthLedger trace endpoint ∧
      PkgSig bundle endpoint pkg

theorem CharacterTheoryRootBHistSurface_root_carrier_obligation
    {group vector action trace provenance : BHist} :
    GroupSingletonCarrier group ->
      ModuleSingletonCarrier vector ->
        Cont group vector action ->
          Cont action BHist.Empty trace ->
            hsame provenance trace ->
              GroupSingletonCarrier group ∧ ModuleSingletonCarrier vector ∧
                UnaryHistory action ∧ UnaryHistory trace ∧ hsame provenance trace ∧
                  Cont group vector action ∧ Cont action BHist.Empty trace := by
  intro groupCarrier vectorCarrier actionRow traceRow provenanceTrace
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm groupCarrier)
  have vectorUnary : UnaryHistory vector :=
    unary_transport unary_empty (hsame_symm vectorCarrier)
  have actionUnary : UnaryHistory action :=
    unary_cont_closed groupUnary vectorUnary actionRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed actionUnary unary_empty traceRow
  exact
    ⟨groupCarrier, vectorCarrier, actionUnary, traceUnary, provenanceTrace, actionRow, traceRow⟩

theorem CharacterTheoryRootBHistSurface_root_classifier_obligation
    {group group' vector vector' action trace trace' provenance : BHist} :
    GroupSingletonCarrier group ->
      ModuleSingletonCarrier vector ->
        hsame group group' ->
          hsame vector vector' ->
            Cont group' vector' action ->
              Cont action BHist.Empty trace' ->
                hsame trace trace' ->
                  hsame provenance trace ->
                    GroupSingletonCarrier group' ∧ ModuleSingletonCarrier vector' ∧
                      UnaryHistory action ∧ UnaryHistory trace' ∧ hsame provenance trace' ∧
                        Cont group' vector' action ∧ Cont action BHist.Empty trace' := by
  intro groupCarrier vectorCarrier sameGroup sameVector actionRow traceRow sameTrace provenanceTrace
  have groupCarrier' : GroupSingletonCarrier group' :=
    hsame_trans (hsame_symm sameGroup) groupCarrier
  have vectorCarrier' : ModuleSingletonCarrier vector' :=
    hsame_trans (hsame_symm sameVector) vectorCarrier
  have groupUnary' : UnaryHistory group' :=
    unary_transport unary_empty (hsame_symm groupCarrier')
  have vectorUnary' : UnaryHistory vector' :=
    unary_transport unary_empty (hsame_symm vectorCarrier')
  have actionUnary : UnaryHistory action :=
    unary_cont_closed groupUnary' vectorUnary' actionRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed actionUnary unary_empty traceRow
  have provenanceTrace' : hsame provenance trace' :=
    hsame_trans provenanceTrace sameTrace
  exact
    ⟨groupCarrier', vectorCarrier', actionUnary, traceUnary', provenanceTrace', actionRow, traceRow⟩

theorem CharacterTheoryRootBHistSurface_carrier_obligation [AskSetup] [PackageSetup]
    {group vector action trace orthLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CharacterTheoryRootBHistSurface group vector action trace orthLedger endpoint bundle pkg ->
      UnaryHistory group ∧ UnaryHistory vector ∧ UnaryHistory action ∧ UnaryHistory trace ∧
        UnaryHistory orthLedger ∧ UnaryHistory endpoint ∧ hsame action (append group vector) ∧
          hsame orthLedger (append action trace) ∧
            hsame endpoint (append orthLedger trace) ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have actionUnary : UnaryHistory action :=
    unary_cont_closed surface.left surface.right.left surface.right.right.left
  have orthLedgerUnary : UnaryHistory orthLedger :=
    unary_cont_closed actionUnary surface.right.right.right.left
      surface.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed orthLedgerUnary surface.right.right.right.left
      surface.right.right.right.right.right.left
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro actionUnary
        (And.intro surface.right.right.right.left
          (And.intro orthLedgerUnary
            (And.intro endpointUnary
                (And.intro surface.right.right.left
                  (And.intro surface.right.right.right.right.left
                    (And.intro surface.right.right.right.right.right.left
                      surface.right.right.right.right.right.right))))))))

end BEDC.Derived.CharacterTheoryUp
