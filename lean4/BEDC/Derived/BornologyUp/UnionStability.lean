import BEDC.Derived.BornologyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BornologyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BornologyCarrier_bounded_family_union_stability
    {boundedFamily subsetHeredity finiteUnion sourceExposure consumerHandoff transport replay
      provenance localName unionRead subfamilyRead : BHist} :
    BornologyTasteGate_single_carrier_alignment_fields
        (BornologyUp.mk boundedFamily subsetHeredity finiteUnion sourceExposure consumerHandoff
          transport replay provenance localName) =
        [boundedFamily, subsetHeredity, finiteUnion, sourceExposure, consumerHandoff, transport,
          replay, provenance, localName] →
      UnaryHistory boundedFamily →
        UnaryHistory sourceExposure →
          UnaryHistory finiteUnion →
            UnaryHistory subsetHeredity →
              Cont boundedFamily sourceExposure unionRead →
                Cont unionRead subsetHeredity subfamilyRead →
                  UnaryHistory unionRead ∧ UnaryHistory subfamilyRead ∧
                    Cont boundedFamily sourceExposure unionRead ∧
                      Cont unionRead subsetHeredity subfamilyRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fieldRows boundedUnary sourceUnary _finiteUnionUnary subsetUnary unionRoute subfamilyRoute
  cases fieldRows
  have unionUnary : UnaryHistory unionRead :=
    unary_cont_closed boundedUnary sourceUnary unionRoute
  have subfamilyUnary : UnaryHistory subfamilyRead :=
    unary_cont_closed unionUnary subsetUnary subfamilyRoute
  exact ⟨unionUnary, subfamilyUnary, unionRoute, subfamilyRoute⟩

end BEDC.Derived.BornologyUp
