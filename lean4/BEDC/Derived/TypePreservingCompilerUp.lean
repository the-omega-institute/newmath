import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TypePreservingCompilerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

structure TypePreservingCompilerCarrier where
  source : BHist
  target : BHist
  graph : BHist
  extLedger : BHist
  reductionLedger : BHist
  route : BHist
  transport : BHist
  pkg : BHist
  name : BHist
  source_graph_ext : Cont source graph extLedger
  target_reduction_route : Cont target reductionLedger route
  transport_names_ext : hsame transport extLedger
  package_names_route : hsame pkg route
  name_names_ext : hsame name extLedger
  name_names_route : hsame name route

namespace TypePreservingCompilerCarrier

def SourceSpec (p : TypePreservingCompilerCarrier) (row : BHist) : Prop :=
  hsame row p.name ∧ Cont p.source p.graph p.extLedger ∧
    Cont p.target p.reductionLedger p.route

def PatternSpec (p : TypePreservingCompilerCarrier)
    (_typedRoute : Cont p.source p.graph p.extLedger) (row : BHist) : Prop :=
  hsame row p.extLedger ∧ Cont p.source p.graph p.extLedger

def LedgerPolicy (p : TypePreservingCompilerCarrier)
    (_reductionRoute : Cont p.target p.reductionLedger p.route) (row : BHist) : Prop :=
  hsame row p.route ∧ hsame p.pkg p.route ∧ Cont p.target p.reductionLedger p.route

end TypePreservingCompilerCarrier

theorem TypePreservingCompilerCarrier_namecert_obligations
    (p : TypePreservingCompilerCarrier)
    (typedRoute : Cont p.source p.graph p.extLedger)
    (reductionRoute : Cont p.target p.reductionLedger p.route) :
    SemanticNameCert (TypePreservingCompilerCarrier.SourceSpec p)
      (TypePreservingCompilerCarrier.PatternSpec p typedRoute)
      (TypePreservingCompilerCarrier.LedgerPolicy p reductionRoute) hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro p.name
        (And.intro (hsame_refl p.name)
          (And.intro p.source_graph_ext p.target_reduction_route))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro (hsame_trans (hsame_symm same) sourceRow.left) sourceRow.right
    }
    pattern_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.left p.name_names_ext) typedRoute
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.left p.name_names_route)
        (And.intro p.package_names_route reductionRoute)
  }

end BEDC.Derived.TypePreservingCompilerUp
