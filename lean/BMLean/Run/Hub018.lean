import BMLean.Tables
import BMLean.Data.Hub018

namespace BMC

theorem hubOk_018 : hubChunkOk (parseRows BMD.hub018) = true := by native_decide

end BMC
