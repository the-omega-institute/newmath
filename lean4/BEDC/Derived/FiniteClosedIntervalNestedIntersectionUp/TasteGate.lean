import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteClosedIntervalNestedIntersectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteClosedIntervalNestedIntersectionCarrier [AskSetup] [PackageSetup]
    (I S C D W Q E H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory I ∧ UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory D ∧
    UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory T ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem FiniteClosedIntervalNestedIntersectionObligationSurface [AskSetup] [PackageSetup]
    {I S C D W Q E H T P N selectorRead cellRead endpointRead windowRead tailRead
      sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteClosedIntervalNestedIntersectionCarrier I S C D W Q E H T P N bundle pkg →
      Cont I S selectorRead →
        Cont selectorRead C cellRead →
          Cont cellRead D endpointRead →
            Cont endpointRead W windowRead →
              Cont windowRead Q tailRead →
                Cont tailRead E sealRead →
                  Cont sealRead N publicRead →
                    PkgSig bundle publicRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row I ∨ hsame row S ∨ hsame row C ∨ hsame row D ∨
                              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                                hsame row T ∨ hsame row P ∨ hsame row N ∨
                                  hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont I S selectorRead ∧
                              Cont selectorRead C cellRead ∧ Cont cellRead D endpointRead ∧
                                Cont endpointRead W windowRead ∧ Cont windowRead Q tailRead ∧
                                  Cont tailRead E sealRead ∧ Cont sealRead N publicRead ∧
                                    PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: FiniteClosedIntervalNestedIntersectionCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute cellRoute endpointRoute windowRoute tailRoute sealRoute
    publicRoute publicPkg
  obtain ⟨iUnary, sUnary, cUnary, dUnary, wUnary, qUnary, eUnary, _hUnary, _tUnary,
    _pUnary, nUnary, _pkgP, _pkgN⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed iUnary sUnary selectorRoute
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed selectorUnary cUnary cellRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed cellUnary dUnary endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed endpointUnary wUnary windowRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary qUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row S ∨ hsame row C ∨ hsame row D ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I S selectorRead ∧ Cont selectorRead C cellRead ∧
              Cont cellRead D endpointRead ∧ Cont endpointRead W windowRead ∧
                Cont windowRead Q tailRead ∧ Cont tailRead E sealRead ∧
                  Cont sealRead N publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, selectorRoute, cellRoute, endpointRoute, windowRoute,
          tailRoute, sealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.FiniteClosedIntervalNestedIntersectionUp
