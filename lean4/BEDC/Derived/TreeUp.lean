import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

def TreeBHistCarrier
    (root source target edge connected acyclic repr package : BHist) : Prop :=
  GraphContEdge source target edge ∧ UnaryHistory root ∧ Cont root connected source ∧
    hsame acyclic BHist.Empty ∧ Cont edge repr target ∧ hsame package (append source target)

theorem TreeBHistCarrier_obligation_rows
    {root source target edge connected acyclic repr package : BHist} :
    TreeBHistCarrier root source target edge connected acyclic repr package ->
      GraphContEdge source target edge ∧ UnaryHistory root ∧ Cont root connected source ∧
        hsame acyclic BHist.Empty ∧ Cont edge repr target ∧
          hsame package (append source target) ∧
            SemanticNameCert UnaryHistory UnaryHistory UnaryHistory hsame := by
  intro carrier
  have cert : SemanticNameCert UnaryHistory UnaryHistory UnaryHistory hsame :=
    GraphCont_namecert_surface.left
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right cert)))))

end BEDC.Derived.TreeUp
