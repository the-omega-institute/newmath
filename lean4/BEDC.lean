/-
Finite kernel imports are kept separate from derived interface imports.
The kernel boundary is `BEDC.FKernel.*` plus `BEDC.BaseReflection.*`;
`BEDC.Derived.*` modules are licensed objects built over that boundary.
-/

/- Finite kernel. -/
import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Cont.Assoc
import BEDC.FKernel.Cont.AssocSpine
import BEDC.FKernel.Cont.Step
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Cont.Pattern
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Sig
import BEDC.FKernel.Sig.Totality
import BEDC.FKernel.Sig.WitnessChain
import BEDC.FKernel.Sig.SameSig
import BEDC.FKernel.Sig.SameSig.Equivalence
import BEDC.FKernel.Sig.Determinacy
import BEDC.FKernel.Sig.Generation
import BEDC.FKernel.Package
import BEDC.FKernel.Settled
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.ExternalBinary.BitInversion
import BEDC.FKernel.ExternalBinary.Inversion
import BEDC.FKernel.ExternalBinary.Model
import BEDC.FKernel.ExternalBinary.Cancellation
import BEDC.FKernel.Gap
import BEDC.FKernel.NameCert
import BEDC.FKernel.NameCert.Descent
import BEDC.FKernel.NameCert.StabilityMode
import BEDC.FKernel.Unary
import BEDC.BaseReflection

/- Derived interfaces (licensed objects). -/
import BEDC.Derived.IntUp
import BEDC.Derived.BoolUp
import BEDC.Derived.OptionUp
import BEDC.Derived.ProdUp
import BEDC.Derived.SumUp
import BEDC.Derived.ListUp
import BEDC.Derived.MonoidUp
import BEDC.Derived.RatUp
import BEDC.Derived.GroupUp
import BEDC.Derived.PreorderUp
import BEDC.Derived.IntervalUp
