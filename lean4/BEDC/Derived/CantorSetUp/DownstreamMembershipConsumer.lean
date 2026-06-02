import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetDownstreamMembershipConsumer [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead intervalRead endpointRead regularRead sealedRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead →
      Cont prefixRead I intervalRead →
        Cont intervalRead D endpointRead →
          Cont endpointRead R regularRead →
            Cont regularRead E sealedRead →
              Cont sealedRead N namedRead →
                PkgSig bundle P pkg →
                  PkgSig bundle N pkg →
                    UnaryHistory T →
                      UnaryHistory G →
                        UnaryHistory I →
                            UnaryHistory D →
                              UnaryHistory R →
                                UnaryHistory E →
                                  UnaryHistory N →
                                    SemanticNameCert
                                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row T ∨ hsame row G ∨ hsame row I ∨
                                            hsame row D ∨ hsame row R ∨ hsame row E ∨
                                              hsame row sealedRead ∨ hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont endpointRead R regularRead ∧
                                            Cont regularRead E sealedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory prefixRead ∧ UnaryHistory intervalRead ∧
                                        UnaryHistory endpointRead ∧ UnaryHistory regularRead ∧
                                          UnaryHistory sealedRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro prefixRoute intervalRoute endpointRoute regularRoute sealRoute namedRoute pkgP pkgN
    prefixUnary gapUnary intervalUnary endpointUnary regularUnary sealUnary nameUnary
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed prefixUnary gapUnary prefixRoute
  have intervalReadUnary : UnaryHistory intervalRead :=
    unary_cont_closed prefixReadUnary intervalUnary intervalRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalReadUnary endpointUnary endpointRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointReadUnary regularUnary regularRoute
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularReadUnary sealUnary sealRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealedReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row I ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row sealedRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpointRead R regularRead ∧
              Cont regularRead E sealedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularRoute, sealRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, prefixReadUnary, intervalReadUnary, endpointReadUnary, regularReadUnary,
      sealedReadUnary, namedReadUnary⟩

end BEDC.Derived.CantorSetUp
