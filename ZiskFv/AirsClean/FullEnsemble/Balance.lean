import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction
import ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridges
import ZiskFv.AirsClean.FullEnsemble.Balance.MemRowReplayProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.SidecarColumns
import ZiskFv.AirsClean.FullEnsemble.Balance.RowsBridgeFacts
import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence
import ZiskFv.AirsClean.FullEnsemble.Balance.EmbeddedInTrace
import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridges

/-!
# Full Clean ensemble balance projections

T7 needs canonical proofs to consume the full Clean ensemble directly,
rather than family-local ensembles.  This module exposes the first reusable
structural facts from `FullEnsemble.fullRv64imEnsemble`: the concrete table
classification and the balanced operation/memory channel projections.

## Trust note

No axioms.  These lemmas only unpack `EnsembleWitness.BalancedChannels` and
the `fullRv64imEnsemble` table list.

This module is a thin aggregator: it re-exports the declarations that were
split out into the `ZiskFv.AirsClean.FullEnsemble.Balance.*` part modules.
Every consumer that imports `ZiskFv.AirsClean.FullEnsemble.Balance` still
sees the full surface unchanged.
-/
