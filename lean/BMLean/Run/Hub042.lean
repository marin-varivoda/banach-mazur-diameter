import BMLean.Tables
import BMLean.Data.Hub042

namespace BMC

theorem hubOk_042 : hubChunkOk (parseRows BMD.hub042) = true := by native_decide

end BMC
