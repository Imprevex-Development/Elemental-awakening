-- Updated
local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 61) then
					if (Enum <= 30) then
						if (Enum <= 14) then
							if (Enum <= 6) then
								if (Enum <= 2) then
									if (Enum <= 0) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 1) then
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum <= 4) then
									if (Enum == 3) then
										Stk[Inst[2]] = {};
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum == 5) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 7) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum <= 10) then
								if (Enum <= 8) then
									if (Enum > 7) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										Stk[Inst[2]] = Stk[Inst[3]];
									end
								elseif (Enum > 9) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 12) then
								if (Enum == 11) then
									do
										return;
									end
								else
									local DIP;
									local NStk;
									local Upv;
									local List;
									local Cls;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Cls = {};
									for Idx = 1, #Lupvals do
										List = Lupvals[Idx];
										for Idz = 0, #List do
											Upv = List[Idz];
											NStk = Upv[1];
											DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								end
							elseif (Enum == 13) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 22) then
							if (Enum <= 18) then
								if (Enum <= 16) then
									if (Enum == 15) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
									end
								elseif (Enum == 17) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 20) then
								if (Enum == 19) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum > 21) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 26) then
							if (Enum <= 24) then
								if (Enum > 23) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum == 25) then
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 28) then
							if (Enum == 27) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 29) then
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 45) then
						if (Enum <= 37) then
							if (Enum <= 33) then
								if (Enum <= 31) then
									local Edx;
									local Results;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 32) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 35) then
								if (Enum == 34) then
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local Step;
									local Index;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Index = Stk[A];
									Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum == 36) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = not Stk[Inst[3]];
							end
						elseif (Enum <= 41) then
							if (Enum <= 39) then
								if (Enum > 38) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 40) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 43) then
							if (Enum == 42) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							end
						elseif (Enum == 44) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 53) then
						if (Enum <= 49) then
							if (Enum <= 47) then
								if (Enum == 46) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum == 48) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum <= 51) then
							if (Enum == 50) then
								local T;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum > 52) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 57) then
						if (Enum <= 55) then
							if (Enum > 54) then
								local Step;
								local Index;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Index = Stk[A];
								Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 56) then
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 59) then
						if (Enum > 58) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 60) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						local A = Inst[2];
						local Step = Stk[A + 2];
						local Index = Stk[A] + Step;
						Stk[A] = Index;
						if (Step > 0) then
							if (Index <= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						elseif (Index >= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					end
				elseif (Enum <= 92) then
					if (Enum <= 76) then
						if (Enum <= 68) then
							if (Enum <= 64) then
								if (Enum <= 62) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 63) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 66) then
								if (Enum > 65) then
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 67) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 72) then
							if (Enum <= 70) then
								if (Enum > 69) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum > 71) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 74) then
							if (Enum > 73) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum == 75) then
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						else
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 84) then
						if (Enum <= 80) then
							if (Enum <= 78) then
								if (Enum == 77) then
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 79) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 82) then
							if (Enum == 81) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum > 83) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 88) then
						if (Enum <= 86) then
							if (Enum > 85) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum == 87) then
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 90) then
						if (Enum == 89) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum > 91) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 107) then
					if (Enum <= 99) then
						if (Enum <= 95) then
							if (Enum <= 93) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 94) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 97) then
							if (Enum > 96) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 98) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 103) then
						if (Enum <= 101) then
							if (Enum == 100) then
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum > 102) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 105) then
						if (Enum == 104) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
						end
					elseif (Enum > 106) then
						Stk[Inst[2]] = Inst[3];
					else
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 115) then
					if (Enum <= 111) then
						if (Enum <= 109) then
							if (Enum > 108) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 110) then
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 113) then
						if (Enum == 112) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
						else
							local B;
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 114) then
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum <= 119) then
					if (Enum <= 117) then
						if (Enum > 116) then
							Stk[Inst[2]]();
						else
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						end
					elseif (Enum == 118) then
						VIP = Inst[3];
					else
						local A = Inst[2];
						Stk[A] = Stk[A]();
					end
				elseif (Enum <= 121) then
					if (Enum > 120) then
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum > 122) then
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
				else
					local A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!2B3Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0052756E5365727669636503133Q005669727475616C496E7075744D616E6167657203103Q0055736572496E70757453657276696365030A3Q0047756953657276696365030C3Q0054772Q656E53657276696365030F3Q0054656C65706F727453657276696365030B3Q00482Q747053657276696365030B3Q004C6F63616C506C6179657203023Q005F47030C3Q00746172676574506C6179657203043Q004E616D6503053Q004A6F62496403073Q00506C616365496403043Q007469636B026Q002E4003053Q007063612Q6C03043Q007461736B03053Q00737061776E026Q00F03F028Q0003093Q0048656172746265617403073Q00436F2Q6E65637403043Q0073746F70030B3Q00636C69636B42752Q746F6E030D3Q006163746976617465542Q6F6C73030C3Q0073746F70542Q6F6C5370616D03093Q0074657374436C69636B030F3Q00746F2Q676C655265636F2Q6E656374030D3Q00746F2Q676C65416E746941666B03093Q007265636F2Q6E65637403073Q00616E746941666B03103Q007374617274542Q6F6C4379636C696E67030F3Q0073746F70542Q6F6C4379636C696E6703113Q00746F2Q676C65542Q6F6C4379636C696E6703153Q00736574542Q6F6C537769746368496E74657276616C03153Q00676574542Q6F6C537769746368496E74657276616C030D3Q006765744163746976654D6F6465030C3Q00676574542Q6F6C436F756E74030B3Q00676574412Q6C542Q6F6C7303073Q00636C65616E757000FF3Q0012783Q00013Q00206Q000200122Q000200038Q0002000200122Q000100013Q00202Q00010001000200122Q000300046Q00010003000200122Q000200013Q00202Q000200020002001272000400056Q00020004000200122Q000300013Q00202Q00030003000200122Q000500066Q00030005000200122Q000400013Q00202Q00040004000200122Q000600076Q000400060002001278000500013Q00202Q00050005000200122Q000700086Q00050007000200122Q000600013Q00202Q00060006000200122Q000800096Q00060008000200122Q000700013Q00202Q00070007000200126B0009000A4Q005F00070009000200200400083Q000B0012350009000C3Q00200400090009000D00061100090028000100010004763Q002800010012350009000C3Q002004000A0008000E00107B0009000D000A00200400090008000E001235000A000C3Q002004000A000A000D00065E0009002E0001000A0004763Q002E00012Q000B3Q00013Q001235000900013Q00205800090009000F00122Q000A00013Q00202Q000A000A00104Q000B00013Q00122Q000C00116Q000C0001000200122Q000D00126Q000E00013Q002Q06000F3Q000100042Q00073Q000E4Q00073Q00084Q00073Q00024Q00073Q000C3Q002Q0600100001000100052Q00073Q000B4Q00073Q00064Q00073Q000A4Q00073Q00094Q00073Q00084Q0027001100113Q001235001200133Q002Q0600130002000100052Q00073Q00114Q00078Q00073Q00084Q00073Q000B4Q00073Q00104Q000E0012000200012Q0027001200123Q001235001300133Q002Q0600140003000100042Q00073Q00124Q00073Q00064Q00073Q000B4Q00073Q00104Q000E0013000200012Q0027001300133Q001235001400133Q002Q0600150004000100042Q00073Q00134Q00073Q00084Q00073Q000B4Q00073Q00104Q000E0014000200012Q0027001400143Q001235001500143Q002004001500150015002Q0600160005000100022Q00073Q000B4Q00073Q00104Q00160015000200024Q001400156Q001500153Q00122Q001600143Q00202Q001600160015002Q0600170006000100042Q00073Q000E4Q00073Q000D4Q00073Q000C4Q00073Q000F4Q00530016000200022Q0007001500163Q002Q0600160007000100022Q00073Q00024Q00073Q00043Q002Q0600170008000100022Q00073Q00084Q00073Q00164Q006F00188Q00198Q001A8Q001B8Q001C001C3Q00122Q001D00163Q00122Q001E00163Q002Q06001F0009000100032Q00073Q001A4Q00073Q00184Q00073Q00193Q002Q060020000A000100022Q00073Q001B4Q00073Q001C3Q002Q060021000B000100012Q00073Q00083Q002Q060022000C000100082Q00073Q00204Q00073Q001B4Q00073Q001C4Q00073Q00084Q00073Q00214Q00073Q001D4Q00073Q001E4Q00073Q00023Q002Q060023000D000100062Q00073Q00184Q00073Q00014Q00073Q001A4Q00073Q00084Q00073Q00024Q00073Q00193Q002Q060024000E000100062Q00073Q001F4Q00073Q00204Q00073Q00084Q00073Q00224Q00073Q001A4Q00073Q00233Q002Q060025000F000100042Q00073Q00084Q00073Q001A4Q00073Q001B4Q00073Q00243Q001201002600173Q00122Q002700166Q002800283Q00202Q00290001001800202Q002900290019002Q06002B0010000100042Q00073Q00264Q00073Q00274Q00073Q00174Q00073Q00244Q005F0029002B00022Q0007002800293Q002Q0600290011000100052Q00073Q00284Q00073Q001F4Q00073Q00204Q00073Q000B4Q00073Q000E4Q0027002A002A3Q001235002B00133Q002Q06002C00120001000F2Q00073Q002A4Q00073Q00034Q00073Q000C4Q00073Q00294Q00073Q00174Q00073Q001F4Q00073Q00204Q00073Q00244Q00073Q000B4Q00073Q000E4Q00073Q00104Q00073Q001B4Q00073Q00214Q00073Q00224Q00073Q001E4Q0014002B000200014Q002B00256Q002B000100014Q002B3Q001100102Q002B001A002900102Q002B001B001700102Q002B001C002400102Q002B001D001F002Q06002C0013000100012Q00073Q00163Q00107B002B001E002C002Q06002C0014000100012Q00073Q000B3Q00107B002B001F002C002Q06002C0015000100012Q00073Q000E3Q001052002B0020002C00102Q002B0021001000102Q002B0022000F00102Q002B0023002200102Q002B00240020002Q06002C0016000100042Q00073Q001B4Q00073Q00204Q00073Q00214Q00073Q00223Q00107B002B0025002C002Q06002C0017000100012Q00073Q001E3Q00107B002B0026002C002Q06002C0018000100012Q00073Q001E3Q00107B002B0027002C002Q06002C0019000100022Q00073Q001B4Q00073Q001A3Q00107B002B0028002C002Q06002C001A000100012Q00073Q00213Q00107B002B0029002C00107B002B002A0021002Q06002C001B000100092Q00073Q00284Q00073Q00114Q00073Q00124Q00073Q00134Q00073Q002A4Q00073Q00144Q00073Q00154Q00073Q001F4Q00073Q00203Q00107B002B002B002C001235002C00143Q002004002C002C0015002Q06002D001C000100022Q00073Q002B4Q00073Q00244Q000E002C000200012Q0017002B00024Q000B3Q00013Q001D3Q00013Q0003053Q007063612Q6C000B4Q00547Q0006113Q0004000100010004763Q000400012Q000B3Q00013Q0012353Q00013Q002Q0600013Q000100032Q00543Q00014Q00543Q00024Q00543Q00034Q000E3Q000200012Q000B3Q00013Q00013Q00243Q0003083Q004765744D6F75736503093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903043Q006D61746803063Q0072616E646F6D026Q0049C0026Q00494003123Q0053656E644D6F7573654D6F76654576656E7403043Q0067616D6503043Q00456E756D03073Q004B6579436F646503093Q004C6566745368696674030A3Q0052696768745368696674030B3Q004C656674436F6E74726F6C030C3Q005269676874436F6E74726F6C026Q00F03F030C3Q0053656E644B65794576656E7403043Q007461736B03043Q0077616974029A5Q99B93F030A3Q0043616D6572615479706503063Q00437573746F6D03093Q00436861726163746572030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403083Q00522Q6F745061727403063Q00434672616D6503063Q00416E676C65732Q033Q00726164026Q00F0BF028Q0003043Q007469636B007D4Q00327Q00206Q00016Q0002000200122Q000100023Q00202Q00010001000300202Q00010001000400202Q00010001000500202Q00010001000600122Q000200023Q00202Q00020002000300202Q00020002000400202Q00020002000700202Q00020002000600122Q000300083Q00202Q00030003000900122Q0004000A3Q00122Q0005000B6Q0003000500024Q00030001000300122Q000400083Q00202Q00040004000900122Q0005000A3Q00122Q0006000B6Q0004000600024Q0004000200044Q000500013Q00202Q00050005000C4Q000700036Q000800043Q00122Q0009000D6Q0005000900014Q000500043Q00122Q0006000E3Q00202Q00060006000F00202Q00060006001000122Q0007000E3Q00202Q00070007000F00202Q00070007001100122Q0008000E3Q00202Q00080008000F00202Q00080008001200122Q0009000E3Q00202Q00090009000F00202Q0009000900134Q000500040001001235000600083Q00201B00060006000900122Q000700146Q000800056Q0006000800024Q0006000500064Q000700013Q00202Q0007000700154Q000900016Q000A00066Q000B5Q00122Q000C000D6Q0007000C000100122Q000700163Q00202Q00070007001700122Q000800186Q0007000200014Q000700013Q00202Q0007000700154Q00098Q000A00066Q000B5Q00122Q000C000D6Q0007000C000100122Q000700023Q00202Q00070007000300062Q0007007900013Q0004763Q007900010020040008000700190012350009000E3Q00200400090009001900200400090009001A00062E00080079000100090004763Q007900012Q005400085Q00200400080008001B0006410008005800013Q0004763Q005800012Q005400085Q00200400080008001B00203B00080008001C00126B000A001D4Q005F0008000A00020006410008007900013Q0004763Q0079000100200400090008001E0006410009007900013Q0004763Q0079000100200400090007001F00122F000A001F3Q00202Q000A000A002000122Q000B00083Q00202Q000B000B002100122Q000C00083Q00202Q000C000C000900122Q000D00223Q00122Q000E00146Q000C000E6Q000B3Q000200122Q000C00083Q00202Q000C000C002100122Q000D00083Q00202Q000D000D000900122Q000E00223Q00122Q000F00146Q000D000F6Q000C3Q000200122Q000D00236Q000A000D00024Q000A0009000A00102Q0007001F000A00122Q000B00163Q00202Q000B000B001700122Q000C00186Q000B0002000100102Q0007001F0009001235000800244Q00770008000100022Q0068000800024Q000B3Q00017Q00043Q0003053Q007063612Q6C03043Q007461736B03043Q0077616974026Q00144000164Q00547Q0006113Q0004000100010004763Q000400012Q000B3Q00013Q0012353Q00013Q002Q0600013Q000100042Q00543Q00014Q00543Q00024Q00543Q00034Q00543Q00044Q00203Q0002000100124Q00023Q00206Q000300122Q000100048Q0002000100124Q00013Q002Q0600010001000100032Q00543Q00014Q00543Q00024Q00543Q00044Q000E3Q000200012Q000B3Q00013Q00023Q00013Q0003173Q0054656C65706F7274546F506C616365496E7374616E636500074Q000F7Q00206Q00014Q000200016Q000300026Q000400038Q000400016Q00017Q00013Q0003083Q0054656C65706F727400064Q000A7Q00206Q00014Q000200016Q000300028Q000300016Q00017Q00023Q00030E3Q00506C6179657252656D6F76696E6703073Q00436F2Q6E656374000A4Q00543Q00013Q0020045Q000100203B5Q0002002Q0600023Q000100032Q00543Q00024Q00543Q00034Q00543Q00044Q005F3Q000200022Q00688Q000B3Q00013Q00013Q00033Q0003043Q007461736B03043Q0077616974027Q0040010D4Q005400015Q00062E3Q000C000100010004763Q000C00012Q0054000100013Q0006410001000C00013Q0004763Q000C0001001235000100013Q00207000010001000200122Q000200036Q0001000200014Q000100026Q0001000100012Q000B3Q00017Q00023Q0003123Q0054656C65706F7274496E69744661696C656403073Q00436F2Q6E65637400094Q00543Q00013Q0020045Q000100203B5Q0002002Q0600023Q000100022Q00543Q00024Q00543Q00034Q005F3Q000200022Q00688Q000B3Q00013Q00013Q00033Q0003043Q007461736B03043Q0077616974026Q000840030A4Q005400035Q0006410003000900013Q0004763Q00090001001235000300013Q00207000030003000200122Q000400036Q0003000200014Q000300016Q0003000100012Q000B3Q00017Q00043Q0003043Q0067616D6503073Q00506C6179657273030E3Q00506C6179657252656D6F76696E6703073Q00436F2Q6E656374000B3Q0012353Q00013Q0020045Q00020020045Q000300203B5Q0004002Q0600023Q000100032Q00543Q00014Q00543Q00024Q00543Q00034Q005F3Q000200022Q00688Q000B3Q00013Q00017Q0001094Q005400015Q00062E3Q0008000100010004763Q000800012Q0054000100013Q0006410001000800013Q0004763Q000800012Q0054000100024Q00750001000100012Q000B3Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q003E4003053Q007063612Q6C000D4Q00547Q0006413Q000C00013Q0004763Q000C00010012353Q00013Q0020045Q000200126B000100034Q000E3Q000200010012353Q00043Q002Q0600013Q000100012Q00543Q00014Q000E3Q000200010004765Q00012Q000B3Q00013Q00013Q00053Q0003043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q00506C6179657273030B3Q004C6F63616C506C61796572000E3Q00126C3Q00013Q00206Q000200122Q000200038Q0002000200064Q000B00013Q0004763Q000B0001001235000100013Q0020040001000100040020040001000100050006110001000D000100010004763Q000D00012Q005400016Q00750001000100012Q000B3Q00017Q00083Q0003043Q007461736B03043Q007761697403043Q007469636B025Q00C0824003043Q006D61746803063Q0072616E646F6D026Q00F03F026Q001040001A4Q00547Q0006413Q001900013Q0004763Q001900010012353Q00013Q0020305Q00024Q000100018Q0002000100124Q00038Q000100024Q000100029Q000001000E2Q0004000F00013Q0004763Q000F00012Q0054000100034Q0075000100010001001235000100053Q00203900010001000600122Q000200073Q00122Q000300086Q00010003000200262Q00013Q000100070004765Q00012Q0054000100034Q00750001000100010004765Q00012Q000B3Q00017Q00033Q0003063Q00506172656E7403073Q0056697369626C6503053Q007063612Q6C012A3Q0006413Q000800013Q0004763Q0008000100200400013Q00010006410001000800013Q0004763Q0008000100200400013Q00020006110001000A000100010004763Q000A00012Q000200016Q0017000100024Q000200015Q001235000200033Q002Q0600033Q000100032Q00078Q00548Q00073Q00014Q000E000200020001001235000200033Q002Q0600030001000100022Q00078Q00073Q00014Q000E000200020001001235000200033Q002Q0600030002000100042Q00543Q00014Q00078Q00548Q00073Q00014Q000E000200020001001235000200033Q002Q0600030003000100022Q00078Q00073Q00014Q000E000200020001001235000200033Q002Q0600030004000100032Q00078Q00548Q00073Q00014Q000E0002000200012Q0017000100024Q000B3Q00013Q00053Q00083Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058027Q004003013Q005903143Q0053656E644D6F75736542752Q746F6E4576656E74028Q00026Q00F03F00219Q003Q00206Q00014Q00015Q00202Q00010001000200202Q00023Q000300202Q00030001000300202Q0003000300044Q00020002000300202Q00033Q000500202Q00040001000500202Q0004000400044Q0003000300044Q000400013Q00202Q0004000400064Q000600026Q000700033Q00122Q000800076Q000900016Q000A5Q00122Q000B00086Q0004000B00014Q000400013Q00202Q0004000400064Q000600026Q000700033Q00122Q000800076Q00098Q000A5Q00122Q000B00086Q0004000B00014Q000400016Q000400028Q00017Q00043Q0003103Q004D6F75736542752Q746F6E31446F776E03043Q0046697265030E3Q004D6F75736542752Q746F6E31557003113Q004D6F75736542752Q746F6E31436C69636B001B4Q00547Q0020045Q00010006413Q000800013Q0004763Q000800012Q00547Q0020045Q000100203B5Q00022Q000E3Q000200012Q00547Q0020045Q00030006413Q001000013Q0004763Q001000012Q00547Q0020045Q000300203B5Q00022Q000E3Q000200012Q00547Q0020045Q00040006413Q001800013Q0004763Q001800012Q00547Q0020045Q000400203B5Q00022Q000E3Q000200012Q00023Q00014Q00683Q00014Q000B3Q00017Q00063Q00030E3Q0053656C65637465644F626A656374030C3Q0053656E644B65794576656E7403043Q00456E756D03073Q004B6579436F646503063Q0052657475726E03043Q0067616D6500184Q00189Q00000100013Q00104Q000100016Q00023Q00206Q00024Q000200013Q00122Q000300033Q00202Q00030003000400202Q0003000300054Q00045Q00122Q000500068Q000500016Q00023Q00206Q00024Q00025Q00122Q000300033Q00202Q00030003000400202Q0003000300054Q00045Q00122Q000500068Q000500016Q00018Q00038Q00017Q00103Q002Q033Q00497341030A3Q005465787442752Q746F6E030B3Q00496D61676542752Q746F6E03163Q004261636B67726F756E645472616E73706172656E637903043Q0053697A6503043Q006D6174682Q033Q006D6178028Q00029A5Q99C93F03053Q005544696D322Q033Q006E657703013Q005803053Q005363616C65026Q66EE3F03063Q004F2Q6673657403013Q0059002F4Q005C7Q00206Q000100122Q000200028Q0002000200064Q000C000100010004763Q000C00012Q00547Q00203B5Q000100126B000200034Q005F3Q000200020006413Q002E00013Q0004763Q002E00012Q00547Q00201A5Q00044Q00015Q00202Q0001000100054Q00025Q00122Q000300063Q00202Q00030003000700122Q000400083Q00202Q00053Q00094Q00030005000200102Q0002000400034Q00025Q00122Q0003000A3Q00202Q00030003000B00202Q00040001000C00202Q00040004000D00202Q00040004000E00202Q00050001000C00202Q00050005000F00202Q00050005000E00202Q00060001001000202Q00060006000D00202Q00060006000E00202Q00070001001000202Q00070007000F00202Q00070007000E4Q00030007000200102Q0002000500034Q00025Q00102Q000200046Q00025Q00102Q0002000500014Q000200016Q000200014Q000B3Q00017Q000A3Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058027Q004003013Q005903123Q0053656E644D6F7573654D6F76654576656E7403043Q0067616D6503143Q0053656E644D6F75736542752Q746F6E4576656E74028Q00026Q00F03F00274Q001D7Q00206Q00014Q00015Q00202Q00010001000200202Q00023Q000300202Q00030001000300202Q0003000300044Q00020002000300202Q00033Q000500202Q00040001000500202Q0004000400044Q0003000300044Q000400013Q00202Q0004000400064Q000600026Q000700033Q00122Q000800076Q0004000800014Q000400013Q00202Q0004000400084Q000600026Q000700033Q00122Q000800096Q000900013Q00122Q000A00073Q00122Q000B000A6Q0004000B00014Q000400013Q00202Q0004000400084Q000600026Q000700033Q00122Q000800096Q00095Q00122Q000A00073Q00122Q000B000A6Q0004000B00014Q000400016Q000400028Q00017Q00103Q00030C3Q0057616974466F724368696C6403093Q00506C61796572477569026Q00144003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q005363722Q656E477569030C3Q0042692Q6C626F617264477569030E3Q0046696E6446697273744368696C6403053Q005374617274030A3Q00506C617942752Q746F6E030A3Q005465787442752Q746F6E030B3Q00496D61676542752Q746F6E03073Q0056697369626C6503063Q00506172656E74029Q00584Q000D7Q00206Q000100122Q000200023Q00122Q000300038Q0003000200064Q0009000100010004763Q000900012Q000200016Q0017000100023Q001235000100043Q00203B00023Q00052Q0047000200034Q005600013Q00030004763Q0053000100203B00060005000600126B000800074Q005F00060008000200061100060018000100010004763Q0018000100203B00060005000600126B000800084Q005F0006000800020006410006005300013Q0004763Q0053000100203B00060005000900126B0008000A4Q005F0006000800020006410006003600013Q0004763Q0036000100203B00070006000900126B0009000B4Q005F0007000900020006410007003600013Q0004763Q0036000100203B00080007000600126B000A000C4Q005F0008000A00020006110008002C000100010004763Q002C000100203B00080007000600126B000A000D4Q005F0008000A00020006410008003600013Q0004763Q0036000100200400080007000E0006410008003600013Q0004763Q0036000100200400080007000F0006410008003600013Q0004763Q003600012Q0054000800014Q0007000900074Q007A000800094Q005900085Q002Q0600073Q000100012Q00073Q00074Q0067000800076Q000900053Q00122Q000A00106Q0008000A000200062Q0008005200013Q0004763Q0052000100203B00090008000600126B000B000C4Q005F0009000B000200061100090048000100010004763Q0048000100203B00090008000600126B000B000D4Q005F0009000B00020006410009005200013Q0004763Q0052000100200400090008000E0006410009005200013Q0004763Q0052000100200400090008000F0006410009005200013Q0004763Q005200012Q0054000900014Q0007000A00084Q007A0009000A4Q005900096Q002B00065Q0006190001000E000100020004763Q000E00012Q000200016Q0017000100024Q000B3Q00013Q00013Q000B3Q00026Q00144003053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503053Q0053746172742Q033Q0049734103053Q004672616D65030E3Q0046696E6446697273744368696C64030A3Q00506C617942752Q746F6E03093Q004775694F626A656374026Q00F03F02283Q000E4200010004000100010004763Q000400012Q0027000200024Q0017000200023Q001235000200023Q00203B00033Q00032Q0047000300044Q005600023Q00040004763Q0023000100200400070006000400266D00070017000100050004763Q0017000100203B00070006000600126B000900074Q005F0007000900020006410007001700013Q0004763Q0017000100203B00070006000800126B000900094Q005F0007000900020006410007001700013Q0004763Q001700012Q0017000700023Q00203B00070006000600126B0009000A4Q005F0007000900020006410007002300013Q0004763Q002300012Q005400076Q0007000800063Q00200800090001000B2Q005F0007000900020006410007002300013Q0004763Q002300012Q0017000700023Q00061900020009000100020004763Q000900012Q0027000200024Q0017000200024Q000B3Q00017Q00033Q0003053Q007061697273030A3Q00446973636F2Q6E6563742Q00114Q00249Q007Q00124Q00016Q000100018Q0002000200044Q000C00010006410004000C00013Q0004763Q000C000100203B0005000400022Q000E0005000200012Q0054000500013Q00204A0005000300030006193Q0006000100020004763Q000600012Q00038Q00683Q00024Q000B3Q00017Q00013Q0003053Q007063612Q6C000C4Q00028Q00688Q00543Q00013Q0006413Q000B00013Q0004763Q000B00010012353Q00013Q002Q0600013Q000100012Q00543Q00014Q000E3Q000200012Q00278Q00683Q00014Q000B3Q00013Q00013Q00053Q0003063Q00747970656F6603063Q0074687265616403043Q007461736B03063Q0063616E63656C030A3Q00446973636F2Q6E656374000E3Q0012353Q00014Q005400016Q00533Q0002000200266D3Q000A000100020004763Q000A00010012353Q00033Q0020045Q00042Q005400016Q000E3Q000200010004763Q000D00012Q00547Q00203B5Q00052Q000E3Q000200012Q000B3Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403083Q004261636B7061636B03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03053Q007461626C6503063Q00696E7365727403093Q00436861726163746572002F4Q00719Q0000015Q00202Q00010001000100122Q000300026Q00010003000200062Q0001001800013Q0004763Q00180001001235000200033Q00203B0003000100042Q0047000300044Q005600023Q00040004763Q0016000100203B00070006000500126B000900064Q005F0007000900020006410007001600013Q0004763Q00160001001235000700073Q0020040007000700082Q000700086Q0007000900064Q00630007000900010006190002000C000100020004763Q000C00012Q005400025Q0020040002000200090006410002002D00013Q0004763Q002D0001001235000300033Q00203B0004000200042Q0047000400054Q005600033Q00050004763Q002B000100203B00080007000500126B000A00064Q005F0008000A00020006410008002B00013Q0004763Q002B0001001235000800073Q0020040008000800082Q000700096Q0007000A00074Q00630008000A000100061900030021000100020004763Q002100012Q00173Q00024Q000B3Q00017Q00023Q0003043Q007461736B03053Q00737061776E00104Q003C9Q003Q000100016Q00018Q00013Q00124Q00013Q00206Q0002002Q0600013Q000100062Q00543Q00014Q00543Q00034Q00543Q00044Q00543Q00054Q00543Q00064Q00543Q00074Q00533Q000200022Q00683Q00024Q000B3Q00013Q00013Q00033Q0003053Q007063612Q6C03043Q007461736B03043Q007761697400124Q00547Q0006413Q001100013Q0004763Q001100010012353Q00013Q002Q0600013Q000100062Q00543Q00014Q00543Q00024Q00543Q00034Q00543Q00044Q00548Q00543Q00054Q00643Q0002000100124Q00023Q00206Q00034Q000100048Q0002000100046Q00012Q000B3Q00013Q00013Q00173Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964027Q004003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03053Q007063612Q6C03043Q007461736B03043Q0077616974029A5Q99B93F03083Q004261636B7061636B03053Q007461626C6503063Q00696E73657274028Q00026Q00F03F026Q002440029A5Q99A93F03063Q00506172656E74029A5Q99E93F03043Q007469636B027B14AE47E17A843F007B4Q00547Q0020045Q00010006413Q007A00013Q0004763Q007A000100203B00013Q000200126B000300034Q005F0001000300020006410001007900013Q0004763Q007900012Q0054000200014Q00770002000100022Q0045000300023Q000E1500040079000100030004763Q007900012Q0027000300033Q00124C000400053Q00202Q00053Q00064Q000500066Q00043Q000600044Q001B000100203B00090008000700126B000B00084Q005F0009000B00020006410009001B00013Q0004763Q001B00012Q0007000300083Q0004763Q001D000100061900040014000100020004763Q001400010006410003002700013Q0004763Q00270001001235000400093Q002Q0600053Q000100012Q00073Q00014Q001200040002000100122Q0004000A3Q00202Q00040004000B00122Q0005000C6Q0004000200012Q000300046Q001300055Q00202Q00050005000200122Q0007000D6Q00050007000200062Q0005003F00013Q0004763Q003F0001001235000600053Q00203B0007000500062Q0047000700084Q005600063Q00080004763Q003D000100203B000B000A000700126B000D00084Q005F000B000D0002000641000B003D00013Q0004763Q003D0001001235000B000E3Q002004000B000B000F2Q0007000C00044Q0007000D000A4Q0063000B000D000100061900060033000100020004763Q003300012Q0045000600043Q000E4200100079000100060004763Q007900012Q0054000600024Q0045000700043Q00064000070048000100060004763Q0048000100126B000600114Q0068000600024Q0054000600024Q00610006000400060006410006007500013Q0004763Q00750001001235000700093Q002Q0600080001000100022Q00073Q00014Q00073Q00064Q002300070002000100122Q000700113Q00122Q000800123Q00122Q000900113Q00042Q0007005E0001001235000B000A3Q00205A000B000B000B00122Q000C00136Q000B0002000100202Q000B0006001400062Q000B005D00013Q0004763Q005D00010004763Q005E000100043D0007005500012Q0054000700033Q00201E000700070015001235000800164Q00770008000100022Q0054000900043Q0006410009007500013Q0004763Q00750001001235000900164Q00770009000100022Q004B00090009000800064000090075000100070004763Q00750001001235000900093Q002Q06000A0002000100032Q00073Q00064Q00078Q00543Q00054Q004D00090002000100122Q0009000A3Q00202Q00090009000B00122Q000A00176Q00090002000100044Q006200012Q0054000700023Q0020080007000700112Q0068000700024Q002B00066Q002B00016Q000B3Q00013Q00033Q00013Q00030C3Q00556E6571756970542Q6F6C7300044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q00013Q0003093Q004571756970542Q6F6C00054Q00267Q00206Q00014Q000200018Q000200016Q00017Q00023Q0003063Q00506172656E7403053Q007063612Q6C00194Q00547Q0006413Q001800013Q0004763Q001800012Q00547Q0020045Q00012Q0054000100013Q00062E3Q0018000100010004763Q001800010012353Q00023Q002Q0600013Q000100012Q00548Q000E3Q000200010012353Q00023Q002Q0600010001000100012Q00543Q00024Q000E3Q000200010012353Q00023Q002Q0600010002000100012Q00548Q000E3Q000200010012353Q00023Q002Q0600010003000100012Q00548Q000E3Q000200012Q000B3Q00013Q00043Q00013Q0003083Q00416374697661746500044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q000A3Q0003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903143Q0053656E644D6F75736542752Q746F6E4576656E74028Q0003043Q0067616D65026Q00F03F001B3Q0012793Q00013Q00206Q000200202Q00013Q000300202Q00010001000400202Q00010001000500202Q00023Q000300202Q00020002000600202Q0002000200054Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q000800013Q00122Q000900093Q00122Q000A000A6Q0003000A00014Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q00085Q00122Q000900093Q00122Q000A000A6Q0003000A00016Q00017Q00083Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030B3Q0052656D6F74654576656E74030A3Q0046697265536572766572030E3Q0052656D6F746546756E6374696F6E03043Q007461736B03053Q00737061776E001C3Q00122A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q0019000100203B00050004000300126B000700044Q005F0005000700020006410005000E00013Q0004763Q000E000100203B0005000400052Q000E0005000200010004763Q0018000100203B00050004000300126B000700064Q005F0005000700020006410005001800013Q0004763Q00180001001235000500073Q002004000500050008002Q0600063Q000100012Q00073Q00044Q000E0005000200012Q002B00035Q0006193Q0006000100020004763Q000600012Q000B3Q00013Q00013Q00013Q0003053Q007063612Q6C00053Q0012353Q00013Q002Q0600013Q000100012Q00548Q000E3Q000200012Q000B3Q00013Q00013Q00013Q00030C3Q00496E766F6B6553657276657200044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q00053Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F7203053Q007063612Q6C00133Q00122A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q0010000100203B00050004000300126B000700044Q005F0005000700020006410005000F00013Q0004763Q000F0001001235000500053Q002Q0600063Q000100012Q00073Q00044Q000E0005000200012Q002B00035Q0006193Q0006000100020004763Q000600012Q000B3Q00013Q00013Q00013Q0003053Q00436C69636B00044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q00043Q0003043Q004E616D6503053Q007063612Q6C03093Q0048656172746265617403073Q00436F2Q6E656374011B3Q0006113Q0003000100010004763Q000300012Q000B3Q00013Q00200400013Q00012Q005400026Q00610002000200010006410002000D00013Q0004763Q000D0001001235000200023Q002Q0600033Q000100022Q00548Q00073Q00014Q000E0002000200012Q005400026Q0054000300013Q00200400030003000300203B000300030004002Q0600050001000100042Q00543Q00024Q00078Q00543Q00034Q00543Q00044Q00290003000500024Q0002000100034Q000200056Q000200018Q00013Q00023Q00013Q00030A3Q00446973636F2Q6E65637400064Q002D9Q00000100019Q00000100206Q00016Q000200016Q00017Q00023Q0003063Q00506172656E7403053Q007063612Q6C00124Q00547Q0006413Q000A00013Q0004763Q000A00012Q00543Q00013Q0006413Q000A00013Q0004763Q000A00012Q00543Q00013Q0020045Q00010006113Q000B000100010004763Q000B00012Q000B3Q00013Q0012353Q00023Q002Q0600013Q000100032Q00543Q00024Q00543Q00014Q00543Q00034Q000E3Q000200012Q000B3Q00013Q00013Q00033Q0003093Q0043686172616374657203063Q00506172656E7403053Q007063612Q6C00224Q00547Q0020045Q00010006113Q0005000100010004763Q000500012Q000B3Q00014Q0054000100013Q00200400010001000200062E0001002100013Q0004763Q00210001001235000100033Q002Q0600023Q000100012Q00543Q00014Q000E000100020001001235000100033Q002Q0600020001000100012Q00543Q00024Q000E000100020001001235000100033Q002Q0600020002000100012Q00543Q00014Q000E000100020001001235000100033Q002Q0600020003000100012Q00543Q00014Q000E000100020001001235000100033Q002Q0600020004000100012Q00543Q00014Q000E000100020001001235000100033Q002Q0600020005000100012Q00543Q00014Q000E0001000200012Q000B3Q00013Q00063Q00013Q0003083Q00416374697661746500044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q000A3Q0003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903143Q0053656E644D6F75736542752Q746F6E4576656E74028Q0003043Q0067616D65026Q00F03F001B3Q0012793Q00013Q00206Q000200202Q00013Q000300202Q00010001000400202Q00010001000500202Q00023Q000300202Q00020002000600202Q0002000200054Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q000800013Q00122Q000900093Q00122Q000A000A6Q0003000A00014Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q00085Q00122Q000900093Q00122Q000A000A6Q0003000A00016Q00017Q00023Q0003093Q0041637469766174656403083Q00416374697661746500084Q00547Q0020045Q00010006413Q000700013Q0004763Q000700012Q00547Q00203B5Q00022Q000E3Q000200012Q000B3Q00017Q00083Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030B3Q0052656D6F74654576656E74030A3Q0046697265536572766572030E3Q0052656D6F746546756E6374696F6E03043Q007461736B03053Q00737061776E001C3Q00122A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q0019000100203B00050004000300126B000700044Q005F0005000700020006410005000E00013Q0004763Q000E000100203B0005000400052Q000E0005000200010004763Q0018000100203B00050004000300126B000700064Q005F0005000700020006410005001800013Q0004763Q00180001001235000500073Q002004000500050008002Q0600063Q000100012Q00073Q00044Q000E0005000200012Q002B00035Q0006193Q0006000100020004763Q000600012Q000B3Q00013Q00013Q00013Q0003053Q007063612Q6C00053Q0012353Q00013Q002Q0600013Q000100012Q00548Q000E3Q000200012Q000B3Q00013Q00013Q00013Q00030C3Q00496E766F6B6553657276657200044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q00053Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F7203053Q007063612Q6C00133Q00122A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q0010000100203B00050004000300126B000700044Q005F0005000700020006410005000F00013Q0004763Q000F0001001235000500053Q002Q0600063Q000100012Q00073Q00044Q000E0005000200012Q002B00035Q0006193Q0006000100020004763Q000600012Q000B3Q00013Q00013Q00013Q0003053Q00436C69636B00044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q00073Q00030E3Q0046696E6446697273744368696C6403063Q0048616E646C6503053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F7203053Q007063612Q6C00184Q00137Q00206Q000100122Q000200028Q0002000200064Q001700013Q0004763Q00170001001235000100033Q00203B00023Q00042Q0047000200034Q005600013Q00030004763Q0015000100203B00060005000500126B000800064Q005F0006000800020006410006001400013Q0004763Q00140001001235000600073Q002Q0600073Q000100012Q00073Q00054Q000E0006000200012Q002B00045Q0006190001000B000100020004763Q000B00012Q000B3Q00013Q00013Q00013Q0003053Q00436C69636B00044Q00547Q00203B5Q00012Q000E3Q000200012Q000B3Q00017Q00113Q00030C3Q0057616974466F724368696C6403083Q004261636B7061636B026Q00144003093Q0043686172616374657203083Q0048756D616E6F696403053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03053Q007461626C6503063Q00696E73657274028Q00027Q004003043Q007461736B03053Q00737061776E03043Q0077616974029A5Q99B93F00664Q003E9Q003Q000100016Q00018Q000100016Q00023Q00206Q000100122Q000200023Q00122Q000300038Q0003000200064Q000C000100010004763Q000C00012Q000B3Q00014Q0054000100023Q00200400010001000400061100010011000100010004763Q001100012Q000B3Q00013Q00203B00020001000100126B000400053Q00126B000500034Q005F00020005000200061100020018000100010004763Q001800012Q000B3Q00014Q000300035Q00124C000400063Q00202Q00053Q00074Q000500066Q00043Q000600044Q0028000100203B00090008000800126B000B00094Q005F0009000B00020006410009002800013Q0004763Q002800010012350009000A3Q00200400090009000B2Q0007000A00034Q0007000B00084Q00630009000B00010006190004001E000100020004763Q001E00012Q000300045Q00124C000500063Q00202Q0006000100074Q000600076Q00053Q000700044Q003A000100203B000A0009000800126B000C00094Q005F000A000C0002000641000A003A00013Q0004763Q003A0001001235000A000A3Q002004000A000A000B2Q0007000B00044Q0007000C00094Q0063000A000C000100061900050030000100020004763Q003000012Q0045000500034Q0045000600044Q003300050005000600266D000500420001000C0004763Q004200012Q000B3Q00013Q000E15000D0047000100050004763Q004700012Q0054000600034Q00750006000100010004763Q006500012Q0002000600014Q001F000600043Q00122Q000600066Q000700046Q00060002000800044Q005000012Q0054000B00054Q0007000C000A4Q000E000B000200010006190006004D000100020004763Q004D0001001235000600064Q0007000700034Q001C0006000200080004763Q00630001001235000B000E3Q002004000B000B000F002Q06000C3Q000100042Q00073Q00024Q00073Q000A4Q00073Q00014Q00543Q00054Q000C000B0002000100122Q000B000E3Q00202Q000B000B001000122Q000C00116Q000B000200014Q00095Q00061900060056000100020004763Q005600012Q000B3Q00013Q00013Q00013Q0003053Q007063612Q6C00083Q0012353Q00013Q002Q0600013Q000100042Q00548Q00543Q00014Q00543Q00024Q00543Q00034Q000E3Q000200012Q000B3Q00013Q00013Q00073Q0003093Q004571756970542Q6F6C026Q00F03F026Q00344003043Q007461736B03043Q0077616974029A5Q99A93F03063Q00506172656E7400204Q00377Q00206Q00014Q000200018Q0002000100124Q00023Q00122Q000100033Q00122Q000200023Q00044Q00170001001235000400043Q00203A00040004000500122Q000500066Q0004000200014Q000400013Q00202Q0004000400074Q000500023Q00062Q00040013000100050004763Q001300010004763Q001700010004763Q0016000100266D00030016000100030004763Q001600012Q000B3Q00013Q00043D3Q000800012Q00543Q00013Q0020045Q00072Q0054000100023Q00062E3Q001F000100010004763Q001F00012Q00543Q00034Q0054000100014Q000E3Q000200012Q000B3Q00017Q00043Q00030C3Q0057616974466F724368696C6403083Q004261636B7061636B026Q00144003053Q007063612Q6C001C4Q00517Q00206Q000100122Q000200023Q00122Q000300038Q0003000200064Q001200013Q0004763Q001200012Q0027000100023Q001235000300043Q002Q0600043Q000100062Q00073Q00014Q00078Q00543Q00014Q00543Q00024Q00543Q00034Q00073Q00024Q000E0003000200012Q002B00016Q0027000100013Q001235000200043Q002Q0600030001000100052Q00073Q00014Q00548Q00543Q00014Q00543Q00024Q00543Q00034Q000E0002000200012Q000B3Q00013Q00023Q00033Q00030A3Q004368696C64412Q64656403073Q00436F2Q6E656374030C3Q004368696C6452656D6F76656400134Q00543Q00013Q0020045Q000100203B5Q0002002Q0600023Q000100032Q00543Q00024Q00543Q00034Q00543Q00044Q00383Q000200029Q006Q00013Q00206Q000300206Q0002002Q0600020001000100032Q00543Q00024Q00543Q00034Q00543Q00044Q005F3Q000200022Q00683Q00054Q000B3Q00013Q00023Q00053Q002Q033Q0049734103043Q00542Q6F6C03043Q007461736B03043Q0077616974029A5Q99B93F01123Q00203B00013Q000100126B000300024Q005F0001000300020006410001001100013Q0004763Q001100012Q005400015Q0006110001000B000100010004763Q000B00012Q0054000100013Q0006410001001100013Q0004763Q00110001001235000100033Q00207000010001000400122Q000200056Q0001000200014Q000100026Q0001000100012Q000B3Q00017Q00053Q002Q033Q0049734103043Q00542Q6F6C03043Q007461736B03043Q0077616974029A5Q99B93F01123Q00203B00013Q000100126B000300024Q005F0001000300020006410001001100013Q0004763Q001100012Q005400015Q0006110001000B000100010004763Q000B00012Q0054000100013Q0006410001001100013Q0004763Q00110001001235000100033Q00207000010001000400122Q000200056Q0001000200014Q000100026Q0001000100012Q000B3Q00017Q00023Q00030E3Q00436861726163746572412Q64656403073Q00436F2Q6E656374000A4Q00543Q00013Q0020045Q000100203B5Q0002002Q0600023Q000100032Q00543Q00024Q00543Q00034Q00543Q00044Q005F3Q000200022Q00688Q000B3Q00013Q00013Q00033Q0003043Q007461736B03043Q0077616974027Q0040010D4Q005400015Q00061100010006000100010004763Q000600012Q0054000100013Q0006410001000C00013Q0004763Q000C0001001235000100013Q00207000010001000200122Q000200036Q0001000200014Q000100026Q0001000100012Q000B3Q00017Q00023Q0003043Q007469636B03053Q007063612Q6C000F3Q00124E3Q00018Q000100024Q00018Q00013Q00014Q000200013Q00062Q0002000E000100010004763Q000E00012Q00687Q001235000100023Q002Q0600023Q000100032Q00543Q00024Q00543Q00034Q00543Q00014Q000E0001000200012Q000B3Q00013Q00013Q00043Q0003043Q007461736B03043Q0077616974027Q0040026Q001440000D4Q00548Q00773Q000100020006413Q000C00013Q0004763Q000C0001001235000100013Q00207000010001000200122Q000200036Q0001000200014Q000100016Q00010001000100126B000100044Q0068000100024Q000B3Q00017Q00013Q0003053Q007063612Q6C000D3Q0012353Q00013Q002Q0600013Q000100012Q00548Q00343Q000200016Q00018Q000100016Q00028Q000100019Q006Q00039Q008Q00048Q00013Q00013Q00013Q00030A3Q00446973636F2Q6E65637400094Q00547Q0006413Q000800013Q0004763Q000800012Q00547Q00203B5Q00012Q000E3Q000200012Q00278Q00688Q000B3Q00017Q00023Q00030A3Q00496E707574426567616E03073Q00436F2Q6E65637400144Q00543Q00013Q0020045Q000100203B5Q0002002Q0600023Q0001000D2Q00543Q00024Q00543Q00034Q00543Q00044Q00543Q00054Q00543Q00064Q00543Q00074Q00543Q00084Q00543Q00094Q00543Q000A4Q00543Q000B4Q00543Q000C4Q00543Q000D4Q00543Q000E4Q005F3Q000200022Q00688Q000B3Q00013Q00013Q000F3Q0003043Q007469636B03073Q004B6579436F646503043Q00456E756D2Q033Q00456E6403043Q00486F6D6503063Q0044656C65746503063Q00496E7365727403063Q0050616765557003083Q0050616765446F776E03023Q00463103023Q004632027Q004003023Q004633026Q00F03F026Q00E03F016F3Q001260000100016Q0001000100024Q00015Q00202Q00013Q000200122Q000200033Q00202Q00020002000200202Q00020002000400062Q0001000C000100020004763Q000C00012Q0054000100014Q00750001000100010004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000500062E00010015000100020004763Q001500012Q0054000100024Q00750001000100010004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000600062E00010020000100020004763Q002000012Q0054000100034Q00750001000100012Q0054000100044Q00750001000100010004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000700062E00010029000100020004763Q002900012Q0054000100054Q00750001000100010004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000800062E00010033000100020004763Q003300012Q0054000100064Q0025000100014Q0068000100063Q0004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000900062E0001003D000100020004763Q003D00012Q0054000100074Q0025000100014Q0068000100073Q0004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000A00062E00010046000100020004763Q004600012Q0054000100084Q00750001000100010004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000B00062E0001005A000100020004763Q005A00012Q0054000100093Q0006410001005200013Q0004763Q005200012Q0054000100044Q00750001000100010004763Q006E00012Q00540001000A4Q00770001000100022Q0045000200013Q000E15000C006E000100020004763Q006E00012Q00540002000B4Q00750002000100010004763Q006E000100200400013Q0002001235000200033Q00200400020002000200200400020002000D00062E0001006E000100020004763Q006E00012Q00540001000C3Q00266D000100660001000E0004763Q0066000100126B0001000F4Q00680001000C3Q0004763Q006E00012Q00540001000C3Q00266D0001006C0001000F0004763Q006C000100126B0001000C4Q00680001000C3Q0004763Q006E000100126B0001000E4Q00680001000C4Q000B3Q00019Q002Q0001054Q006A00018Q00028Q000100026Q00019Q0000019Q003Q00044Q00548Q00258Q00688Q000B3Q00019Q003Q00044Q00548Q00258Q00688Q000B3Q00017Q00013Q00027Q0040000E4Q00547Q0006413Q000600013Q0004763Q000600012Q00543Q00014Q00753Q000100010004763Q000D00012Q00543Q00024Q00773Q000100022Q004500015Q000E150001000D000100010004763Q000D00012Q0054000100034Q00750001000100012Q000B3Q00017Q00033Q0003043Q007479706503063Q006E756D626572028Q0001093Q001235000100014Q000700026Q005300010002000200266D00010008000100020004763Q00080001000E420003000800013Q0004763Q000800012Q00688Q000B3Q00019Q003Q00034Q00548Q00173Q00024Q000B3Q00017Q00033Q0003073Q006379636C696E6703043Q007370616D03083Q00696E616374697665000F4Q00547Q0006413Q000600013Q0004763Q0006000100126B3Q00014Q00173Q00023Q0004763Q000E00012Q00543Q00013Q0006413Q000C00013Q0004763Q000C000100126B3Q00024Q00173Q00023Q0004763Q000E000100126B3Q00034Q00173Q00024Q000B3Q00019Q003Q00054Q00669Q003Q000100029Q006Q00028Q00017Q00013Q0003053Q007063612Q6C000D3Q0012353Q00013Q002Q0600013Q000100092Q00548Q00543Q00014Q00543Q00024Q00543Q00034Q00543Q00044Q00543Q00054Q00543Q00064Q00543Q00074Q00543Q00084Q000E3Q000200012Q000B3Q00013Q00013Q00053Q00030A3Q00446973636F2Q6E65637403063Q00747970656F6603063Q0074687265616403043Q007461736B03063Q0063616E63656C00354Q00547Q0006413Q000600013Q0004763Q000600012Q00547Q00203B5Q00012Q000E3Q000200012Q00543Q00013Q0006413Q000C00013Q0004763Q000C00012Q00543Q00013Q00203B5Q00012Q000E3Q000200012Q00543Q00023Q0006413Q001200013Q0004763Q001200012Q00543Q00023Q00203B5Q00012Q000E3Q000200012Q00543Q00033Q0006413Q001800013Q0004763Q001800012Q00543Q00033Q00203B5Q00012Q000E3Q000200012Q00543Q00043Q0006413Q001E00013Q0004763Q001E00012Q00543Q00043Q00203B5Q00012Q000E3Q000200010012353Q00024Q0054000100054Q00533Q0002000200266D3Q0027000100030004763Q002700010012353Q00043Q0020045Q00052Q0054000100054Q000E3Q000200010012353Q00024Q0054000100064Q00533Q0002000200266D3Q0030000100030004763Q003000010012353Q00043Q0020045Q00052Q0054000100064Q000E3Q000200012Q00543Q00074Q00753Q000100012Q00543Q00084Q00753Q000100012Q000B3Q00017Q00013Q0003053Q007063612Q6C000C3Q0012353Q00013Q00023100016Q001C3Q000200010006115Q000100010004765Q0001001235000200013Q002Q0600030001000100022Q00548Q00543Q00014Q000E0002000200010004765Q00012Q000B3Q00013Q00023Q00033Q0003043Q007461736B03043Q0077616974026Q00F03F00053Q0012283Q00013Q00206Q000200122Q000100038Q000200016Q00017Q00043Q0003073Q00636C65616E757003043Q007461736B03043Q0077616974026Q00F03F000A4Q005D7Q00206Q00016Q0001000100124Q00023Q00206Q000300122Q000100048Q000200016Q00018Q000100016Q00017Q00", GetFEnv(), ...);
