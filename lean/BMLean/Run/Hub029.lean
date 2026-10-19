import BMLean.Tables
import BMLean.Data.Hub029

namespace BMC

theorem hubOk_029 : hubChunkOk (parseRows BMD.hub029) = true := by native_decide

end BMC
