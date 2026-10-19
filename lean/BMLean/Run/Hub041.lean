import BMLean.Tables
import BMLean.Data.Hub041

namespace BMC

theorem hubOk_041 : hubChunkOk (parseRows BMD.hub041) = true := by native_decide

end BMC
