import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

protected theorem ListClassifierSpec_carrier_transport_from_nameCert
    {Carrier : BEDC.FKernel.Hist.BHist -> Prop}
    {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop}
    (cert : BEDC.FKernel.NameCert.NameCert Carrier sameA) :
    forall {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
      (forall {x : BEDC.FKernel.Hist.BHist}, x ∈ xs -> Carrier x) ->
        ListClassifierSpec sameA xs ys ->
          forall {y : BEDC.FKernel.Hist.BHist}, y ∈ ys -> Carrier y := by
  intro xs
  induction xs with
  | nil =>
      intro ys _entries same y mem
      cases ys with
      | nil =>
          cases mem
      | cons _ _ =>
          cases same
  | cons x xs ih =>
      intro ys entries same y mem
      cases ys with
      | nil =>
          cases same
      | cons yHead ys =>
          cases same with
          | intro headSame tailSame =>
              cases mem with
              | head =>
                  exact cert.carrier_respects_equiv headSame
                    (entries (x := x) (List.Mem.head xs))
              | tail _ tailMem =>
                  have tailEntries :
                      forall {z : BEDC.FKernel.Hist.BHist}, z ∈ xs -> Carrier z := by
                    intro z memZ
                    exact entries (x := z) (List.Mem.tail x memZ)
                  exact ih tailEntries tailSame tailMem

end BEDC.Derived.ListUp
