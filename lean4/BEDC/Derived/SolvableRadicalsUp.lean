import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SolvableRadicalsUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SolvableRadicalsTowerStep_obligation
    {baseField nextField rootIndex radicand stepExtension towerLedger : BHist} :
    UnaryHistory baseField ->
      UnaryHistory nextField ->
        UnaryHistory rootIndex ->
          UnaryHistory radicand ->
            Cont rootIndex radicand stepExtension ->
              Cont baseField nextField towerLedger ->
                UnaryHistory stepExtension ∧ UnaryHistory towerLedger ∧
                  hsame stepExtension (append rootIndex radicand) ∧
                    hsame towerLedger (append baseField nextField) := by
  intro baseUnary nextUnary rootUnary radicandUnary stepRow towerRow
  have stepUnary : UnaryHistory stepExtension :=
    unary_cont_closed rootUnary radicandUnary stepRow
  have towerUnary : UnaryHistory towerLedger :=
    unary_cont_closed baseUnary nextUnary towerRow
  constructor
  · exact stepUnary
  constructor
  · exact towerUnary
  constructor
  · exact stepRow
  · exact towerRow

end BEDC.Derived.SolvableRadicalsUp
