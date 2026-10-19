import BMLean.Tables
import BMLean.Data.Hub002

namespace BMC

theorem hubOk_002 : hubChunkOk (parseRows BMD.hub002) = true := by native_decide

end BMC
