signature CHIALISP_STRUCTS =
sig
end

signature CHIALISP =
sig
    include CHIALISP_STRUCTS

    val readSsaJson: String.t -> unit
end
