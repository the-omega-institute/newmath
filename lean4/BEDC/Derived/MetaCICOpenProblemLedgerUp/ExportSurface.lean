import BEDC.Derived.MetaCICOpenProblemLedgerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem MetaCICOpenProblemLedgerExportSurface_encode_append (S C : BHist) :
    metaCICOpenProblemLedgerEncodeBHist (append S C) =
      List.append (metaCICOpenProblemLedgerEncodeBHist C)
        (metaCICOpenProblemLedgerEncodeBHist S) := by
  -- BEDC touchpoint anchor: BHist BMark append
  induction C with
  | Empty =>
      rfl
  | e0 C ih =>
      exact congrArg (fun tail => BMark.b0 :: tail) ih
  | e1 C ih =>
      exact congrArg (fun tail => BMark.b1 :: tail) ih

end BEDC.Derived.MetaCICOpenProblemLedgerUp
