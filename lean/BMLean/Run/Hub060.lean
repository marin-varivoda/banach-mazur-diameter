import BMLean.Tables
import BMLean.Data.Hub060

namespace BMC

theorem hubOk_060 : hubChunkOk (parseRows BMD.hub060) = true := by native_decide

end BMC
