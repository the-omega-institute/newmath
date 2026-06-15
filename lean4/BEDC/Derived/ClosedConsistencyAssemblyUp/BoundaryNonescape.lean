import BEDC.Derived.ClosedConsistencyAssemblyUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ClosedConsistencyAssemblyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ClosedConsistencyAssembly_boundary_nonescape
    {x : ClosedConsistencyAssemblyUp} {boundaryRead replayRead : BHist} :
    boundaryRead ∈ closedConsistencyAssemblyFields x →
      Cont boundaryRead boundaryRead replayRead →
        SemanticNameCert
            (fun row : BHist => row ∈ closedConsistencyAssemblyFields x ∨ hsame row replayRead)
            (fun row : BHist => row ∈ closedConsistencyAssemblyFields x)
            (fun row : BHist => row ∈ closedConsistencyAssemblyFields x ∨ hsame row replayRead)
            hsame ∧
          UnaryHistory boundaryRead →
            UnaryHistory replayRead →
              Cont boundaryRead boundaryRead replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro boundaryMember replayCont
  intro _certAndBoundary _unaryReplay
  cases replayCont
  rfl

end BEDC.Derived.ClosedConsistencyAssemblyUp
