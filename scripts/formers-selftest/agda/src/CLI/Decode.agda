-- fixture: the decoder's tag wall, carrying tags that are NOT formers
decodeExp j =
    if tag is "lift" then just liftᵉ
    else if tag is "defer" then just deferᵉ
    else if tag is "sharedSig" then just sharedSigᵉ
    else if tag is "natT" then just nat̂
    else if tag is "nat" then nothing   -- a TYPE tag, and not a former

decodePrim j =
    if op is "add" then just add
    else if op is "not" then just notᵖ
    else nothing
