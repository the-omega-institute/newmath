import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyPositivePartUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyPositivePartCarrier [AskSetup] [PackageSetup]
    (source zero window dyadicSource dyadicZero absCompat maxRow readback realSeal
      transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory zero ∧ UnaryHistory window ∧
    UnaryHistory dyadicSource ∧ UnaryHistory dyadicZero ∧ UnaryHistory absCompat ∧
      UnaryHistory maxRow ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory localName ∧ Cont source zero window ∧
            Cont window dyadicSource maxRow ∧ Cont maxRow readback realSeal ∧
              Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg

theorem RegularCauchyPositivePartCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source zero window dyadicSource dyadicZero absCompat maxRow readback realSeal
      transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyPositivePartCarrier source zero window dyadicSource dyadicZero absCompat
      maxRow readback realSeal transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyPositivePartCarrier source zero window dyadicSource dyadicZero
            absCompat maxRow readback realSeal transport replay provenance localName bundle pkg ∧
            hsame row localName)
        (fun row : BHist =>
          hsame row source ∨ hsame row zero ∨ hsame row window ∨ hsame row maxRow ∨
            hsame row readback ∨ hsame row realSeal ∨ hsame row localName)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localName pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert
  intro packet
  have carrierPacket := packet
  obtain
    ⟨unarySource, unaryZero, unaryWindow, unaryDyadicSource, unaryDyadicZero,
      unaryAbsCompat, unaryMaxRow, unaryReadback, unaryRealSeal, unaryTransport,
      unaryReplay, unaryProvenance, unaryLocalName, routeWindow, routeMaxRow,
      routeRealSeal, routeProvenance, pkgProvenance, pkgLocalName⟩ := packet
  have sourceAtLocal :
        RegularCauchyPositivePartCarrier source zero window dyadicSource dyadicZero
          absCompat maxRow readback realSeal transport replay provenance localName bundle pkg ∧
        hsame localName localName :=
    ⟨carrierPacket, hsame_refl localName⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro localName sourceAtLocal
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
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨unary_transport unaryLocalName (hsame_symm sourceRow.right), pkgLocalName⟩
  }

end BEDC.Derived.RegularCauchyPositivePartUp
