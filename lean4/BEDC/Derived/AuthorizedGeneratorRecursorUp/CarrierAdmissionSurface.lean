import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_admission_surface [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg /\
              hsame row N)
          (fun row : BHist =>
            hsame row I \/ hsame row E \/ hsame row M \/ hsame row B \/
              hsame row D \/ hsame row O \/ hsame row A \/ hsame row H \/
                hsame row C \/ hsame row P \/ hsame row G \/ hsame row N)
          (fun row : BHist => PkgSig bundle P pkg /\ hsame row N) hsame /\
        (exists packet : AuthorizedGeneratorRecursorUp,
          packet = AuthorizedGeneratorRecursorUp.mk I E M B D O A H C P G N /\
            authorizedGeneratorRecursorFromEventFlow
                (authorizedGeneratorRecursorToEventFlow packet) =
              some packet) /\
          UnaryHistory I /\ UnaryHistory E /\ UnaryHistory M /\ UnaryHistory B /\
            UnaryHistory D /\ UnaryHistory O /\ UnaryHistory A /\ UnaryHistory H /\
              UnaryHistory C /\ UnaryHistory P /\ UnaryHistory G /\ UnaryHistory N /\
                Cont I E M /\ Cont M B D /\ Cont D O A /\ hsame H (append A C) /\
                  PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg NameCert SemanticNameCert hsame Cont
  intro carrier
  have carrierRows :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg :=
    carrier
  obtain ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
    unaryP, unaryG, unaryN, routeIEM, routeMBD, routeDOA, sameH, pkgP⟩ := carrier
  have sourceN :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg /\
        hsame N N :=
    ⟨carrierRows, hsame_refl N⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg /\
              hsame row N)
          (fun row : BHist =>
            hsame row I \/ hsame row E \/ hsame row M \/ hsame row B \/
              hsame row D \/ hsame row O \/ hsame row A \/ hsame row H \/
                hsame row C \/ hsame row P \/ hsame row G \/ hsame row N)
          (fun row : BHist => PkgSig bundle P pkg /\ hsame row N) hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr source.right))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨pkgP, source.right⟩
  }
  have packetWitness :
      exists packet : AuthorizedGeneratorRecursorUp,
        packet = AuthorizedGeneratorRecursorUp.mk I E M B D O A H C P G N /\
          authorizedGeneratorRecursorFromEventFlow (authorizedGeneratorRecursorToEventFlow packet) =
            some packet := by
    refine Exists.intro (AuthorizedGeneratorRecursorUp.mk I E M B D O A H C P G N) ?_
    exact ⟨rfl, AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk I E M B D O A H C P G N)⟩
  exact
    ⟨cert, packetWitness, unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH,
      unaryC, unaryP, unaryG, unaryN, routeIEM, routeMBD, routeDOA, sameH, pkgP⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
