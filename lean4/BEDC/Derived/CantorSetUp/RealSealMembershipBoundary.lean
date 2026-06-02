import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetRealSealMembershipBoundary [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead endpointRead regularRead sealedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead →
      Cont prefixRead D endpointRead →
        Cont endpointRead R regularRead →
          Cont regularRead E sealedRead →
            Cont sealedRead N namedRead →
              UnaryHistory T →
                UnaryHistory G →
                  UnaryHistory D →
                    UnaryHistory R →
                      UnaryHistory E →
                        UnaryHistory N →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row prefixRead ∨ hsame row endpointRead ∨
                                      hsame row regularRead ∨ hsame row sealedRead ∨
                                        hsame row namedRead ∨ hsame row P ∨ hsame row N)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont prefixRead D endpointRead ∧
                                      Cont endpointRead R regularRead ∧
                                        Cont regularRead E sealedRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory prefixRead ∧ UnaryHistory endpointRead ∧
                                  UnaryHistory regularRead ∧ UnaryHistory sealedRead ∧
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixRoute endpointRoute regularRoute sealRoute namedRoute prefixUnary gapUnary
    endpointUnary regularUnary sealUnary nameUnary pkgP pkgN
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed prefixUnary gapUnary prefixRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed prefixReadUnary endpointUnary endpointRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointReadUnary regularUnary regularRoute
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularReadUnary sealUnary sealRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealedReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row prefixRead ∨ hsame row endpointRead ∨ hsame row regularRead ∨
              hsame row sealedRead ∨ hsame row namedRead ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont prefixRead D endpointRead ∧
              Cont endpointRead R regularRead ∧ Cont regularRead E sealedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedReadUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, regularRoute, sealRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, prefixReadUnary, endpointReadUnary, regularReadUnary, sealedReadUnary,
      namedReadUnary⟩

end BEDC.Derived.CantorSetUp
