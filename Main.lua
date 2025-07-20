--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

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
				if (Enum <= 60) then
					if (Enum <= 29) then
						if (Enum <= 14) then
							if (Enum <= 6) then
								if (Enum <= 2) then
									if (Enum <= 0) then
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
									elseif (Enum > 1) then
										local Results;
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
										local B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 4) then
									if (Enum == 3) then
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
								elseif (Enum == 5) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
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
							elseif (Enum <= 10) then
								if (Enum <= 8) then
									if (Enum == 7) then
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
										local A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum > 9) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								else
									local Results;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							elseif (Enum == 13) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 21) then
							if (Enum <= 17) then
								if (Enum <= 15) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								elseif (Enum > 16) then
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
							elseif (Enum <= 19) then
								if (Enum == 18) then
									Stk[Inst[2]]();
								else
									local Results;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							elseif (Enum > 20) then
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
						elseif (Enum <= 25) then
							if (Enum <= 23) then
								if (Enum == 22) then
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								else
									local Results;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							elseif (Enum == 24) then
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
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							end
						elseif (Enum <= 27) then
							if (Enum == 26) then
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
						elseif (Enum > 28) then
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
					elseif (Enum <= 44) then
						if (Enum <= 36) then
							if (Enum <= 32) then
								if (Enum <= 30) then
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
								elseif (Enum == 31) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
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
										if (Mvm[1] == 56) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum <= 34) then
								if (Enum == 33) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
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
							elseif (Enum == 35) then
								VIP = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum > 37) then
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
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
							elseif (Enum > 39) then
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
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 42) then
							if (Enum > 41) then
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
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 43) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
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
					elseif (Enum <= 52) then
						if (Enum <= 48) then
							if (Enum <= 46) then
								if (Enum > 45) then
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
								else
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								end
							elseif (Enum == 47) then
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
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 50) then
							if (Enum == 49) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
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
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum > 51) then
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
					elseif (Enum <= 56) then
						if (Enum <= 54) then
							if (Enum > 53) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum > 55) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 58) then
						if (Enum > 57) then
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
						end
					elseif (Enum > 59) then
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
						do
							return;
						end
					end
				elseif (Enum <= 91) then
					if (Enum <= 75) then
						if (Enum <= 67) then
							if (Enum <= 63) then
								if (Enum <= 61) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 62) then
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
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								end
							elseif (Enum <= 65) then
								if (Enum == 64) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
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
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 66) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
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
							end
						elseif (Enum <= 71) then
							if (Enum <= 69) then
								if (Enum > 68) then
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
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum > 70) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
							end
						elseif (Enum <= 73) then
							if (Enum == 72) then
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
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 74) then
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
					elseif (Enum <= 83) then
						if (Enum <= 79) then
							if (Enum <= 77) then
								if (Enum == 76) then
									Stk[Inst[2]] = Env[Inst[3]];
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
								end
							elseif (Enum == 78) then
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
						elseif (Enum <= 81) then
							if (Enum == 80) then
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
						elseif (Enum > 82) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						end
					elseif (Enum <= 87) then
						if (Enum <= 85) then
							if (Enum == 84) then
								do
									return Stk[Inst[2]];
								end
							else
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
							end
						elseif (Enum > 86) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
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
						end
					elseif (Enum <= 89) then
						if (Enum > 88) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum == 90) then
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
					else
						do
							return;
						end
					end
				elseif (Enum <= 106) then
					if (Enum <= 98) then
						if (Enum <= 94) then
							if (Enum <= 92) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Enum > 93) then
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
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 96) then
							if (Enum > 95) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
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
						elseif (Enum > 97) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 102) then
						if (Enum <= 100) then
							if (Enum > 99) then
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
						elseif (Enum > 101) then
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
						else
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
						end
					elseif (Enum <= 104) then
						if (Enum == 103) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
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
						end
					elseif (Enum == 105) then
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
				elseif (Enum <= 114) then
					if (Enum <= 110) then
						if (Enum <= 108) then
							if (Enum > 107) then
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
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum == 109) then
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
					elseif (Enum <= 112) then
						if (Enum == 111) then
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
						else
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
						end
					elseif (Enum == 113) then
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
					end
				elseif (Enum <= 118) then
					if (Enum <= 116) then
						if (Enum > 115) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum > 117) then
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
				elseif (Enum <= 120) then
					if (Enum == 119) then
						Stk[Inst[2]] = #Stk[Inst[3]];
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
				elseif (Enum > 121) then
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
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!293Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0052756E5365727669636503133Q005669727475616C496E7075744D616E6167657203103Q0055736572496E70757453657276696365030A3Q0047756953657276696365030C3Q0054772Q656E53657276696365030F3Q0054656C65706F727453657276696365030B3Q00482Q747053657276696365030B3Q0046612Q6E79446179313233030B3Q004C6F63616C506C6179657203053Q004A6F62496403073Q00506C616365496403043Q007469636B026Q002E40030E3Q00506C6179657252656D6F76696E6703073Q00436F2Q6E65637403123Q0054656C65706F7274496E69744661696C656403053Q00737061776E026Q00F03F028Q0003093Q00486561727462656174030A3Q00496E707574426567616E03043Q0073746F70030B3Q00636C69636B42752Q746F6E030D3Q006163746976617465542Q6F6C73030C3Q0073746F70542Q6F6C5370616D03093Q0074657374436C69636B030F3Q00746F2Q676C655265636F2Q6E656374030D3Q00746F2Q676C65416E746941666B03093Q007265636F2Q6E65637403073Q00616E746941666B03103Q007374617274542Q6F6C4379636C696E67030F3Q0073746F70542Q6F6C4379636C696E6703113Q00746F2Q676C65542Q6F6C4379636C696E6703153Q00736574542Q6F6C537769746368496E74657276616C03153Q00676574542Q6F6C537769746368496E74657276616C030D3Q006765744163746976654D6F6465030C3Q00676574542Q6F6C436F756E74030B3Q00676574412Q6C542Q6F6C7300D83Q00127A3Q00013Q00206Q000200122Q000200038Q0002000200122Q000100013Q00202Q00010001000200122Q000300046Q00010003000200122Q000200013Q00202Q000200020002001272000400056Q00020004000200122Q000300013Q00202Q00030003000200122Q000500066Q00030005000200122Q000400013Q00202Q00040004000200122Q000600076Q00040006000200127A000500013Q00202Q00050005000200122Q000700086Q00050007000200122Q000600013Q00202Q00060006000200122Q000800096Q00060008000200122Q000700013Q00202Q00070007000200120D0009000A4Q004000070009000200120D0008000B3Q00201500093Q000C00122Q000A00013Q00202Q000A000A000D00122Q000B00013Q00202Q000B000B000E4Q000C00013Q00122Q000D000F6Q000D0001000200122Q000E00106Q000F00013Q00062000103Q000100042Q00383Q000F4Q00383Q00094Q00383Q00024Q00383Q000D3Q00062000110001000100052Q00383Q000C4Q00383Q00064Q00383Q000B4Q00383Q000A4Q00383Q00093Q00062000120002000100022Q00383Q000C4Q00383Q00113Q00062000130003000100022Q00383Q000C4Q00383Q00113Q00202400143Q001100202Q0014001400124Q001600126Q00140016000100202Q00140006001300202Q0014001400124Q001600136Q00140016000100122Q001400013Q00202Q00140014000300200E00140014001100200100140014001200062000160004000100032Q00383Q00094Q00383Q000C4Q00383Q00114Q004700140016000100124C001400143Q00062000150005000100022Q00383Q000C4Q00383Q00114Q003500140002000100124C001400143Q00062000150006000100042Q00383Q000F4Q00383Q000E4Q00383Q000D4Q00383Q00104Q003500140002000100062000140007000100022Q00383Q00024Q00383Q00043Q00062000150008000100022Q00383Q00094Q00383Q00144Q000300168Q00178Q00188Q00198Q001A001A3Q00122Q001B00153Q00122Q001C00153Q000620001D0009000100032Q00383Q00184Q00383Q00164Q00383Q00173Q000620001E000A000100022Q00383Q00194Q00383Q001A3Q000620001F000B000100012Q00383Q00093Q0006200020000C000100082Q00383Q001E4Q00383Q00194Q00383Q001A4Q00383Q00094Q00383Q001F4Q00383Q001B4Q00383Q001C4Q00383Q00023Q0006200021000D000100062Q00383Q00164Q00383Q00014Q00383Q00184Q00383Q00094Q00383Q00024Q00383Q00173Q0006200022000E000100062Q00383Q001D4Q00383Q001E4Q00383Q00094Q00383Q00204Q00383Q00184Q00383Q00213Q0006200023000F000100042Q00383Q00094Q00383Q00184Q00383Q00194Q00383Q00223Q001248002400163Q00122Q002500156Q002600263Q00202Q00270001001700202Q00270027001200062000290010000100042Q00383Q00244Q00383Q00254Q00383Q00154Q00383Q00224Q00400027002900022Q0038002600273Q00062000270011000100052Q00383Q00264Q00383Q001D4Q00383Q001E4Q00383Q000C4Q00383Q000F3Q00200E002800030018002001002800280012000620002A00120001000D2Q00383Q000D4Q00383Q00274Q00383Q00154Q00383Q001D4Q00383Q001E4Q00383Q00224Q00383Q000C4Q00383Q000F4Q00383Q00114Q00383Q00194Q00383Q001F4Q00383Q00204Q00383Q001C4Q00340028002A00014Q002800236Q0028000100014Q00283Q001100102Q00280019002700102Q0028001A001500102Q0028001B002200102Q0028001C001D00062000290013000100012Q00383Q00143Q0010730028001D002900062000290014000100012Q00383Q000C3Q0010730028001E002900062000290015000100012Q00383Q000F3Q0010450028001F002900102Q00280020001100102Q00280021001000102Q00280022002000102Q00280023001E00062000290016000100042Q00383Q00194Q00383Q001E4Q00383Q001F4Q00383Q00203Q00107300280024002900062000290017000100012Q00383Q001C3Q00107300280025002900062000290018000100012Q00383Q001C3Q00107300280026002900062000290019000100022Q00383Q00194Q00383Q00183Q0010730028002700290006200029001A000100012Q00383Q001F3Q00107300280028002900107300280029001F2Q0054002800024Q005B3Q00013Q001B3Q00013Q0003053Q007063612Q6C000B4Q00367Q00063D3Q0004000100010004233Q000400012Q005B3Q00013Q00124C3Q00013Q00062000013Q000100032Q00363Q00014Q00363Q00024Q00363Q00034Q00353Q000200012Q005B3Q00013Q00013Q00243Q0003083Q004765744D6F75736503093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903043Q006D61746803063Q0072616E646F6D026Q0049C0026Q00494003123Q0053656E644D6F7573654D6F76654576656E7403043Q0067616D6503043Q00456E756D03073Q004B6579436F646503093Q004C6566745368696674030A3Q0052696768745368696674030B3Q004C656674436F6E74726F6C030C3Q005269676874436F6E74726F6C026Q00F03F030C3Q0053656E644B65794576656E7403043Q007461736B03043Q0077616974029A5Q99B93F030A3Q0043616D6572615479706503063Q00437573746F6D03093Q00436861726163746572030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403083Q00522Q6F745061727403063Q00434672616D6503063Q00416E676C65732Q033Q00726164026Q00F0BF028Q0003043Q007469636B007D4Q00557Q00206Q00016Q0002000200122Q000100023Q00202Q00010001000300202Q00010001000400202Q00010001000500202Q00010001000600122Q000200023Q00202Q00020002000300202Q00020002000400202Q00020002000700202Q00020002000600122Q000300083Q00202Q00030003000900122Q0004000A3Q00122Q0005000B6Q0003000500024Q00030001000300122Q000400083Q00202Q00040004000900122Q0005000A3Q00122Q0006000B6Q0004000600024Q0004000200044Q000500013Q00202Q00050005000C4Q000700036Q000800043Q00122Q0009000D6Q0005000900014Q000500043Q00122Q0006000E3Q00202Q00060006000F00202Q00060006001000122Q0007000E3Q00202Q00070007000F00202Q00070007001100122Q0008000E3Q00202Q00080008000F00202Q00080008001200122Q0009000E3Q00202Q00090009000F00202Q0009000900134Q00050004000100124C000600083Q00206800060006000900122Q000700146Q000800056Q0006000800024Q0006000500064Q000700013Q00202Q0007000700154Q000900016Q000A00066Q000B5Q00122Q000C000D6Q0007000C000100122Q000700163Q00202Q00070007001700122Q000800186Q0007000200014Q000700013Q00202Q0007000700154Q00098Q000A00066Q000B5Q00122Q000C000D6Q0007000C000100122Q000700023Q00202Q00070007000300062Q0007007900013Q0004233Q0079000100200E00080007001900124C0009000E3Q00200E00090009001900200E00090009001A00064900080079000100090004233Q007900012Q003600085Q00200E00080008001B0006420008005800013Q0004233Q005800012Q003600085Q00200E00080008001B00200100080008001C00120D000A001D4Q00400008000A00020006420008007900013Q0004233Q0079000100200E00090008001E0006420009007900013Q0004233Q0079000100200E00090007001F001276000A001F3Q00202Q000A000A002000122Q000B00083Q00202Q000B000B002100122Q000C00083Q00202Q000C000C000900122Q000D00223Q00122Q000E00146Q000C000E6Q000B3Q000200122Q000C00083Q00202Q000C000C002100122Q000D00083Q00202Q000D000D000900122Q000E00223Q00122Q000F00146Q000D000F6Q000C3Q000200122Q000D00236Q000A000D00024Q000A0009000A00102Q0007001F000A00122Q000B00163Q00202Q000B000B001700122Q000C00186Q000B0002000100102Q0007001F000900124C000800244Q005C0008000100022Q0044000800024Q005B3Q00017Q00043Q0003053Q007063612Q6C03043Q007461736B03043Q0077616974026Q00144000164Q00367Q00063D3Q0004000100010004233Q000400012Q005B3Q00013Q00124C3Q00013Q00062000013Q000100042Q00363Q00014Q00363Q00024Q00363Q00034Q00363Q00044Q00283Q0002000100124Q00023Q00206Q000300122Q000100048Q0002000100124Q00013Q00062000010001000100032Q00363Q00014Q00363Q00024Q00363Q00044Q00353Q000200012Q005B3Q00013Q00023Q00013Q0003173Q0054656C65706F7274546F506C616365496E7374616E636500079Q003Q00206Q00014Q000200016Q000300026Q000400038Q000400016Q00017Q00013Q0003083Q0054656C65706F727400064Q001D7Q00206Q00014Q000200016Q000300028Q000300016Q00017Q00033Q0003043Q007461736B03043Q0077616974027Q0040000A4Q00367Q0006423Q000900013Q0004233Q0009000100124C3Q00013Q0020065Q000200122Q000100038Q000200016Q00018Q000100012Q005B3Q00017Q00033Q0003043Q007461736B03043Q0077616974026Q000840030A4Q003600035Q0006420003000900013Q0004233Q0009000100124C000300013Q00200600030003000200122Q000400036Q0003000200014Q000300016Q0003000100012Q005B3Q00019Q002Q0001094Q003600015Q0006493Q0008000100010004233Q000800012Q0036000100013Q0006420001000800013Q0004233Q000800012Q0036000100024Q00120001000100012Q005B3Q00017Q00043Q0003043Q007461736B03043Q0077616974026Q003E4003053Q007063612Q6C000D4Q00367Q0006423Q000C00013Q0004233Q000C000100124C3Q00013Q00200E5Q000200120D000100034Q00353Q0002000100124C3Q00043Q00062000013Q000100012Q00363Q00014Q00353Q000200010004235Q00012Q005B3Q00013Q00013Q00053Q0003043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q00506C6179657273030B3Q004C6F63616C506C61796572000E3Q0012253Q00013Q00206Q000200122Q000200038Q0002000200064Q000B00013Q0004233Q000B000100124C000100013Q00200E00010001000400200E00010001000500063D0001000D000100010004233Q000D00012Q003600016Q00120001000100012Q005B3Q00017Q00083Q0003043Q007461736B03043Q007761697403043Q007469636B025Q00C0824003043Q006D61746803063Q0072616E646F6D026Q00F03F026Q001040001A4Q00367Q0006423Q001900013Q0004233Q0019000100124C3Q00013Q0020655Q00024Q000100018Q0002000100124Q00038Q000100024Q000100029Q000001000E2Q0004000F00013Q0004233Q000F00012Q0036000100034Q001200010001000100124C000100053Q00204A00010001000600122Q000200073Q00122Q000300086Q00010003000200262Q00013Q000100070004235Q00012Q0036000100034Q00120001000100010004235Q00012Q005B3Q00017Q00033Q0003063Q00506172656E7403073Q0056697369626C6503053Q007063612Q6C012A3Q0006423Q000800013Q0004233Q0008000100200E00013Q00010006420001000800013Q0004233Q0008000100200E00013Q000200063D0001000A000100010004233Q000A00012Q005800016Q0054000100024Q005800015Q00124C000200033Q00062000033Q000100032Q00388Q00368Q00383Q00014Q003500020002000100124C000200033Q00062000030001000100022Q00388Q00383Q00014Q003500020002000100124C000200033Q00062000030002000100042Q00363Q00014Q00388Q00368Q00383Q00014Q003500020002000100124C000200033Q00062000030003000100022Q00388Q00383Q00014Q003500020002000100124C000200033Q00062000030004000100032Q00388Q00368Q00383Q00014Q00350002000200012Q0054000100024Q005B3Q00013Q00053Q00083Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058027Q004003013Q005903143Q0053656E644D6F75736542752Q746F6E4576656E74028Q00026Q00F03F00214Q004D7Q00206Q00014Q00015Q00202Q00010001000200202Q00023Q000300202Q00030001000300202Q0003000300044Q00020002000300202Q00033Q000500202Q00040001000500202Q0004000400044Q0003000300044Q000400013Q00202Q0004000400064Q000600026Q000700033Q00122Q000800076Q000900016Q000A5Q00122Q000B00086Q0004000B00014Q000400013Q00202Q0004000400064Q000600026Q000700033Q00122Q000800076Q00098Q000A5Q00122Q000B00086Q0004000B00014Q000400016Q000400028Q00017Q00043Q0003103Q004D6F75736542752Q746F6E31446F776E03043Q0046697265030E3Q004D6F75736542752Q746F6E31557003113Q004D6F75736542752Q746F6E31436C69636B001B4Q00367Q00200E5Q00010006423Q000800013Q0004233Q000800012Q00367Q00200E5Q00010020015Q00022Q00353Q000200012Q00367Q00200E5Q00030006423Q001000013Q0004233Q001000012Q00367Q00200E5Q00030020015Q00022Q00353Q000200012Q00367Q00200E5Q00040006423Q001800013Q0004233Q001800012Q00367Q00200E5Q00040020015Q00022Q00353Q000200012Q00583Q00014Q00443Q00014Q005B3Q00017Q00063Q00030E3Q0053656C65637465644F626A656374030C3Q0053656E644B65794576656E7403043Q00456E756D03073Q004B6579436F646503063Q0052657475726E03043Q0067616D6500184Q00439Q00000100013Q00104Q000100016Q00023Q00206Q00024Q000200013Q00122Q000300033Q00202Q00030003000400202Q0003000300054Q00045Q00122Q000500068Q000500016Q00023Q00206Q00024Q00025Q00122Q000300033Q00202Q00030003000400202Q0003000300054Q00045Q00122Q000500068Q000500016Q00018Q00038Q00017Q00103Q002Q033Q00497341030A3Q005465787442752Q746F6E030B3Q00496D61676542752Q746F6E03163Q004261636B67726F756E645472616E73706172656E637903043Q0053697A6503043Q006D6174682Q033Q006D6178028Q00029A5Q99C93F03053Q005544696D322Q033Q006E657703013Q005803053Q005363616C65026Q66EE3F03063Q004F2Q6673657403013Q0059002F4Q00467Q00206Q000100122Q000200028Q0002000200064Q000C000100010004233Q000C00012Q00367Q0020015Q000100120D000200034Q00403Q000200020006423Q002E00013Q0004233Q002E00012Q00367Q00206F5Q00044Q00015Q00202Q0001000100054Q00025Q00122Q000300063Q00202Q00030003000700122Q000400083Q00202Q00053Q00094Q00030005000200102Q0002000400034Q00025Q00122Q0003000A3Q00202Q00030003000B00202Q00040001000C00202Q00040004000D00202Q00040004000E00202Q00050001000C00202Q00050005000F00202Q00050005000E00202Q00060001001000202Q00060006000D00202Q00060006000E00202Q00070001001000202Q00070007000F00202Q00070007000E4Q00030007000200102Q0002000500034Q00025Q00102Q000200046Q00025Q00102Q0002000500014Q000200016Q000200014Q005B3Q00017Q000A3Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058027Q004003013Q005903123Q0053656E644D6F7573654D6F76654576656E7403043Q0067616D6503143Q0053656E644D6F75736542752Q746F6E4576656E74028Q00026Q00F03F00274Q00797Q00206Q00014Q00015Q00202Q00010001000200202Q00023Q000300202Q00030001000300202Q0003000300044Q00020002000300202Q00033Q000500202Q00040001000500202Q0004000400044Q0003000300044Q000400013Q00202Q0004000400064Q000600026Q000700033Q00122Q000800076Q0004000800014Q000400013Q00202Q0004000400084Q000600026Q000700033Q00122Q000800096Q000900013Q00122Q000A00073Q00122Q000B000A6Q0004000B00014Q000400013Q00202Q0004000400084Q000600026Q000700033Q00122Q000800096Q00095Q00122Q000A00073Q00122Q000B000A6Q0004000B00014Q000400016Q000400028Q00017Q00103Q00030C3Q0057616974466F724368696C6403093Q00506C61796572477569026Q00144003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q005363722Q656E477569030C3Q0042692Q6C626F617264477569030E3Q0046696E6446697273744368696C6403053Q005374617274030A3Q00506C617942752Q746F6E030A3Q005465787442752Q746F6E030B3Q00496D61676542752Q746F6E03073Q0056697369626C6503063Q00506172656E74029Q00584Q00567Q00206Q000100122Q000200023Q00122Q000300038Q0003000200064Q0009000100010004233Q000900012Q005800016Q0054000100023Q00124C000100043Q00200100023Q00052Q0057000200034Q002900013Q00030004233Q0053000100200100060005000600120D000800074Q004000060008000200063D00060018000100010004233Q0018000100200100060005000600120D000800084Q00400006000800020006420006005300013Q0004233Q0053000100200100060005000900120D0008000A4Q00400006000800020006420006003600013Q0004233Q0036000100200100070006000900120D0009000B4Q00400007000900020006420007003600013Q0004233Q0036000100200100080007000600120D000A000C4Q00400008000A000200063D0008002C000100010004233Q002C000100200100080007000600120D000A000D4Q00400008000A00020006420008003600013Q0004233Q0036000100200E00080007000E0006420008003600013Q0004233Q0036000100200E00080007000F0006420008003600013Q0004233Q003600012Q0036000800014Q0038000900074Q005D000800094Q001F00085Q00062000073Q000100012Q00383Q00074Q003C000800076Q000900053Q00122Q000A00106Q0008000A000200062Q0008005200013Q0004233Q0052000100200100090008000600120D000B000C4Q00400009000B000200063D00090048000100010004233Q0048000100200100090008000600120D000B000D4Q00400009000B00020006420009005200013Q0004233Q0052000100200E00090008000E0006420009005200013Q0004233Q0052000100200E00090008000F0006420009005200013Q0004233Q005200012Q0036000900014Q0038000A00084Q005D0009000A4Q001F00096Q000400065Q0006640001000E000100020004233Q000E00012Q005800016Q0054000100024Q005B3Q00013Q00013Q000B3Q00026Q00144003053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D6503053Q0053746172742Q033Q0049734103053Q004672616D65030E3Q0046696E6446697273744368696C64030A3Q00506C617942752Q746F6E03093Q004775694F626A656374026Q00F03F02283Q000E6000010004000100010004233Q000400012Q002C000200024Q0054000200023Q00124C000200023Q00200100033Q00032Q0057000300044Q002900023Q00040004233Q0023000100200E00070006000400262100070017000100050004233Q0017000100200100070006000600120D000900074Q00400007000900020006420007001700013Q0004233Q0017000100200100070006000800120D000900094Q00400007000900020006420007001700013Q0004233Q001700012Q0054000700023Q00200100070006000600120D0009000A4Q00400007000900020006420007002300013Q0004233Q002300012Q003600076Q0038000800063Q00200500090001000B2Q00400007000900020006420007002300013Q0004233Q002300012Q0054000700023Q00066400020009000100020004233Q000900012Q002C000200024Q0054000200024Q005B3Q00017Q00033Q0003053Q007061697273030A3Q00446973636F2Q6E6563742Q00114Q00719Q007Q00124Q00016Q000100018Q0002000200044Q000C00010006420004000C00013Q0004233Q000C00010020010005000400022Q00350005000200012Q0036000500013Q0020530005000300030006643Q0006000100020004233Q000600012Q00278Q00443Q00024Q005B3Q00017Q00013Q00030A3Q00446973636F2Q6E656374000B4Q00588Q00448Q00363Q00013Q0006423Q000A00013Q0004233Q000A00012Q00363Q00013Q0020015Q00012Q00353Q000200012Q002C8Q00443Q00014Q005B3Q00017Q00093Q00030E3Q0046696E6446697273744368696C6403083Q004261636B7061636B03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03053Q007461626C6503063Q00696E7365727403093Q00436861726163746572002F4Q00789Q0000015Q00202Q00010001000100122Q000300026Q00010003000200062Q0001001800013Q0004233Q0018000100124C000200033Q0020010003000100042Q0057000300044Q002900023Q00040004233Q0016000100200100070006000500120D000900064Q00400007000900020006420007001600013Q0004233Q0016000100124C000700073Q00200E0007000700082Q003800086Q0038000900064Q00470007000900010006640002000C000100020004233Q000C00012Q003600025Q00200E0002000200090006420002002D00013Q0004233Q002D000100124C000300033Q0020010004000200042Q0057000400054Q002900033Q00050004233Q002B000100200100080007000500120D000A00064Q00400008000A00020006420008002B00013Q0004233Q002B000100124C000800073Q00200E0008000800082Q003800096Q0038000A00074Q00470008000A000100066400030021000100020004233Q002100012Q00543Q00024Q005B3Q00017Q00023Q0003043Q007461736B03053Q00737061776E00104Q003F9Q003Q000100016Q00018Q00013Q00124Q00013Q00206Q000200062000013Q000100062Q00363Q00014Q00363Q00034Q00363Q00044Q00363Q00054Q00363Q00064Q00363Q00074Q00613Q000200022Q00443Q00024Q005B3Q00013Q00013Q00173Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964027Q004003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03053Q007063612Q6C03043Q007461736B03043Q0077616974029A5Q99B93F03083Q004261636B7061636B03053Q007461626C6503063Q00696E73657274028Q00026Q00F03F026Q002440029A5Q99A93F03063Q00506172656E74029A5Q99E93F03043Q007469636B027B14AE47E17A843F00914Q00367Q0006423Q009000013Q0004233Q009000012Q00363Q00013Q00200E5Q00010006423Q008B00013Q0004233Q008B000100200100013Q000200120D000300034Q00400001000300020006420001008A00013Q0004233Q008A00012Q0036000200024Q005C0002000100022Q0077000300023Q000E670004008A000100030004233Q008A00012Q002C000300033Q001275000400053Q00202Q00053Q00064Q000500066Q00043Q000600044Q001E000100200100090008000700120D000B00084Q00400009000B00020006420009001E00013Q0004233Q001E00012Q0038000300083Q0004233Q0020000100066400040017000100020004233Q001700010006420003002A00013Q0004233Q002A000100124C000400093Q00062000053Q000100012Q00383Q00014Q006A00040002000100122Q0004000A3Q00202Q00040004000B00122Q0005000C6Q0004000200012Q002700046Q004B000500013Q00202Q00050005000200122Q0007000D6Q00050007000200062Q0005004200013Q0004233Q0042000100124C000600053Q0020010007000500062Q0057000700084Q002900063Q00080004233Q00400001002001000B000A000700120D000D00084Q0040000B000D0002000642000B004000013Q0004233Q0040000100124C000B000E3Q00200E000B000B000F2Q0038000C00044Q0038000D000A4Q0047000B000D000100066400060036000100020004233Q003600012Q0077000600043Q000E600010008A000100060004233Q008A00012Q0036000600034Q0077000700043Q0006620007004B000100060004233Q004B000100120D000600114Q0044000600034Q0036000600034Q002D0006000400060006420006008600013Q0004233Q0086000100124C000700093Q00062000080001000100022Q00383Q00014Q00383Q00064Q005100070002000100122Q000700113Q00122Q000800123Q00122Q000900113Q00042Q00070061000100124C000B000A3Q00206C000B000B000B00122Q000C00136Q000B0002000100202Q000B0006001400062Q000B006000013Q0004233Q006000010004233Q006100010004220007005800012Q0036000700043Q00201900070007001500124C000800164Q005C0008000100022Q003600095Q0006420009008600013Q0004233Q0086000100124C000900164Q005C0009000100022Q000F00090009000800066200090086000100070004233Q0086000100200E0009000600140006490009008100013Q0004233Q0081000100124C000900093Q000620000A0002000100012Q00383Q00064Q003500090002000100124C000900093Q000620000A0003000100012Q00363Q00054Q003500090002000100124C000900093Q000620000A0004000100012Q00383Q00064Q003500090002000100124C000900093Q000620000A0005000100022Q00383Q00064Q00363Q00014Q003500090002000100124C0009000A3Q00200E00090009000B00120D000A00174Q00350009000200010004233Q006500012Q0036000700033Q0020050007000700112Q0044000700034Q000400066Q000400015Q00124C0001000A3Q00200E00010001000B2Q0036000200044Q00350001000200010004235Q00012Q005B3Q00013Q00063Q00013Q00030C3Q00556E6571756970542Q6F6C7300044Q00367Q0020015Q00012Q00353Q000200012Q005B3Q00017Q00013Q0003093Q004571756970542Q6F6C00054Q00107Q00206Q00014Q000200018Q000200016Q00017Q00013Q0003083Q00416374697661746500044Q00367Q0020015Q00012Q00353Q000200012Q005B3Q00017Q000A3Q0003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903143Q0053656E644D6F75736542752Q746F6E4576656E74028Q0003043Q0067616D65026Q00F03F001B3Q0012333Q00013Q00206Q000200202Q00013Q000300202Q00010001000400202Q00010001000500202Q00023Q000300202Q00020002000600202Q0002000200054Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q000800013Q00122Q000900093Q00122Q000A000A6Q0003000A00014Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q00085Q00122Q000900093Q00122Q000A000A6Q0003000A00016Q00017Q00073Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030B3Q0052656D6F74654576656E74030A3Q0046697265536572766572030E3Q0052656D6F746546756E6374696F6E03053Q00737061776E001B3Q00123A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q0018000100200100050004000300120D000700044Q00400005000700020006420005000E00013Q0004233Q000E00010020010005000400052Q00350005000200010004233Q0017000100200100050004000300120D000700064Q00400005000700020006420005001700013Q0004233Q0017000100124C000500073Q00062000063Q000100012Q00383Q00044Q00350005000200012Q000400035Q0006643Q0006000100020004233Q000600012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00053Q00124C3Q00013Q00062000013Q000100012Q00368Q00353Q000200012Q005B3Q00013Q00013Q00013Q00030C3Q00496E766F6B6553657276657200044Q00367Q0020015Q00012Q00353Q000200012Q005B3Q00017Q00083Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F72030E3Q00676574636F2Q6E656374696F6E73030A3Q004D6F757365436C69636B03083Q0046756E6374696F6E03053Q00737061776E00213Q00123A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q001E000100200100050004000300120D000700044Q00400005000700020006420005001E00013Q0004233Q001E000100124C000500013Q001217000600053Q00202Q0007000400064Q000600076Q00053Q000700044Q001C00010006420009001B00013Q0004233Q001B000100200E000A00090007000642000A001B00013Q0004233Q001B000100124C000A00083Q000620000B3Q000100022Q00383Q00094Q00363Q00014Q0035000A000200012Q000400085Q00066400050011000100020004233Q001100010006643Q0006000100020004233Q000600012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00063Q00124C3Q00013Q00062000013Q000100022Q00368Q00363Q00014Q00353Q000200012Q005B3Q00013Q00013Q00013Q0003083Q0046756E6374696F6E00054Q00327Q00206Q00014Q000100018Q000200016Q00017Q00043Q0003043Q004E616D65030A3Q00446973636F2Q6E65637403093Q0048656172746265617403073Q00436F2Q6E656374011A3Q00063D3Q0003000100010004233Q000300012Q005B3Q00013Q00200E00013Q00012Q003600026Q002D0002000200010006420002000C00013Q0004233Q000C00012Q003600026Q002D0002000200010020010002000200022Q00350002000200012Q003600026Q0036000300013Q00200E00030003000300200100030003000400062000053Q000100042Q00363Q00024Q00388Q00363Q00034Q00363Q00044Q00500003000500024Q0002000100034Q000200056Q000200018Q00013Q00013Q00023Q0003063Q00506172656E7403053Q007063612Q6C00124Q00367Q0006423Q000A00013Q0004233Q000A00012Q00363Q00013Q0006423Q000A00013Q0004233Q000A00012Q00363Q00013Q00200E5Q000100063D3Q000B000100010004233Q000B00012Q005B3Q00013Q00124C3Q00023Q00062000013Q000100032Q00363Q00024Q00363Q00014Q00363Q00034Q00353Q000200012Q005B3Q00013Q00013Q00033Q0003093Q0043686172616374657203063Q00506172656E7403053Q007063612Q6C00244Q00367Q00200E5Q000100063D3Q0005000100010004233Q000500012Q005B3Q00014Q0036000100013Q00200E0001000100020006490001002300013Q0004233Q0023000100124C000100033Q00062000023Q000100012Q00363Q00014Q003500010002000100124C000100033Q00062000020001000100012Q00363Q00024Q003500010002000100124C000100033Q00062000020002000100012Q00363Q00014Q003500010002000100124C000100033Q00062000020003000100012Q00363Q00014Q003500010002000100124C000100033Q00062000020004000100022Q00363Q00014Q00368Q003500010002000100124C000100033Q00062000020005000100022Q00363Q00014Q00368Q00350001000200012Q005B3Q00013Q00063Q00013Q0003083Q00416374697661746500044Q00367Q0020015Q00012Q00353Q000200012Q005B3Q00017Q000A3Q0003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503013Q0058027Q004003013Q005903143Q0053656E644D6F75736542752Q746F6E4576656E74028Q0003043Q0067616D65026Q00F03F001B3Q0012333Q00013Q00206Q000200202Q00013Q000300202Q00010001000400202Q00010001000500202Q00023Q000300202Q00020002000600202Q0002000200054Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q000800013Q00122Q000900093Q00122Q000A000A6Q0003000A00014Q00035Q00202Q0003000300074Q000500016Q000600023Q00122Q000700086Q00085Q00122Q000900093Q00122Q000A000A6Q0003000A00016Q00017Q00043Q0003093Q0041637469766174656403053Q007061697273030E3Q00676574636F2Q6E656374696F6E7303083Q0046756E6374696F6E00154Q00367Q00200E5Q00010006423Q001400013Q0004233Q0014000100124C3Q00023Q001209000100036Q00025Q00202Q0002000200014Q000100029Q00000200044Q001200010006420004001200013Q0004233Q0012000100200E0005000400040006420005001200013Q0004233Q0012000100200E0005000400042Q00120005000100010006643Q000B000100020004233Q000B00012Q005B3Q00017Q00073Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030B3Q0052656D6F74654576656E74030A3Q0046697265536572766572030E3Q0052656D6F746546756E6374696F6E03053Q00737061776E001B3Q00123A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q0018000100200100050004000300120D000700044Q00400005000700020006420005000E00013Q0004233Q000E00010020010005000400052Q00350005000200010004233Q0017000100200100050004000300120D000700064Q00400005000700020006420005001700013Q0004233Q0017000100124C000500073Q00062000063Q000100012Q00383Q00044Q00350005000200012Q000400035Q0006643Q0006000100020004233Q000600012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00053Q00124C3Q00013Q00062000013Q000100012Q00368Q00353Q000200012Q005B3Q00013Q00013Q00013Q00030C3Q00496E766F6B6553657276657200044Q00367Q0020015Q00012Q00353Q000200012Q005B3Q00017Q00083Q0003053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F72030E3Q00676574636F2Q6E656374696F6E73030A3Q004D6F757365436C69636B03083Q0046756E6374696F6E03053Q00737061776E00213Q00123A3Q00016Q00015Q00202Q0001000100024Q000100029Q00000200044Q001E000100200100050004000300120D000700044Q00400005000700020006420005001E00013Q0004233Q001E000100124C000500013Q001217000600053Q00202Q0007000400064Q000600076Q00053Q000700044Q001C00010006420009001B00013Q0004233Q001B000100200E000A00090007000642000A001B00013Q0004233Q001B000100124C000A00083Q000620000B3Q000100022Q00383Q00094Q00363Q00014Q0035000A000200012Q000400085Q00066400050011000100020004233Q001100010006643Q0006000100020004233Q000600012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00063Q00124C3Q00013Q00062000013Q000100022Q00368Q00363Q00014Q00353Q000200012Q005B3Q00013Q00013Q00013Q0003083Q0046756E6374696F6E00054Q00327Q00206Q00014Q000100018Q000200016Q00017Q000A3Q00030E3Q0046696E6446697273744368696C6403063Q0048616E646C6503053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F72030E3Q00676574636F2Q6E656374696F6E73030A3Q004D6F757365436C69636B03083Q0046756E6374696F6E03053Q00737061776E00264Q004B7Q00206Q000100122Q000200028Q0002000200064Q002500013Q0004233Q0025000100124C000100033Q00200100023Q00042Q0057000200034Q002900013Q00030004233Q0023000100200100060005000500120D000800064Q00400006000800020006420006002300013Q0004233Q0023000100124C000600033Q001217000700073Q00202Q0008000500084Q000700086Q00063Q000800044Q00210001000642000A002000013Q0004233Q0020000100200E000B000A0009000642000B002000013Q0004233Q0020000100124C000B000A3Q000620000C3Q000100022Q00383Q000A4Q00363Q00014Q0035000B000200012Q000400095Q00066400060016000100020004233Q001600010006640001000B000100020004233Q000B00012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00063Q00124C3Q00013Q00062000013Q000100022Q00368Q00363Q00014Q00353Q000200012Q005B3Q00013Q00013Q00013Q0003083Q0046756E6374696F6E00054Q00327Q00206Q00014Q000100018Q000200016Q00017Q00113Q00030C3Q0057616974466F724368696C6403083Q004261636B7061636B026Q00144003093Q0043686172616374657203083Q0048756D616E6F696403053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03053Q007461626C6503063Q00696E73657274028Q00027Q004003043Q007461736B03053Q00737061776E03043Q0077616974029A5Q99B93F00664Q00709Q003Q000100016Q00018Q000100016Q00023Q00206Q000100122Q000200023Q00122Q000300038Q0003000200064Q000C000100010004233Q000C00012Q005B3Q00014Q0036000100023Q00200E00010001000400063D00010011000100010004233Q001100012Q005B3Q00013Q00200100020001000100120D000400053Q00120D000500034Q004000020005000200063D00020018000100010004233Q001800012Q005B3Q00014Q002700035Q001275000400063Q00202Q00053Q00074Q000500066Q00043Q000600044Q0028000100200100090008000800120D000B00094Q00400009000B00020006420009002800013Q0004233Q0028000100124C0009000A3Q00200E00090009000B2Q0038000A00034Q0038000B00084Q00470009000B00010006640004001E000100020004233Q001E00012Q002700045Q001275000500063Q00202Q0006000100074Q000600076Q00053Q000700044Q003A0001002001000A0009000800120D000C00094Q0040000A000C0002000642000A003A00013Q0004233Q003A000100124C000A000A3Q00200E000A000A000B2Q0038000B00044Q0038000C00094Q0047000A000C000100066400050030000100020004233Q003000012Q0077000500034Q0077000600044Q0059000500050006002621000500420001000C0004233Q004200012Q005B3Q00013Q000E67000D0047000100050004233Q004700012Q0036000600034Q00120006000100010004233Q006500012Q0058000600014Q005A000600043Q00122Q000600066Q000700046Q00060002000800044Q005000012Q0036000B00054Q0038000C000A4Q0035000B000200010006640006004D000100020004233Q004D000100124C000600064Q0038000700034Q00740006000200080004233Q0063000100124C000B000E3Q00200E000B000B000F000620000C3Q000100042Q00383Q00024Q00383Q000A4Q00383Q00014Q00363Q00054Q006A000B0002000100122Q000B000E3Q00202Q000B000B001000122Q000C00116Q000B000200012Q000400095Q00066400060056000100020004233Q005600012Q005B3Q00013Q00013Q00013Q0003053Q007063612Q6C00083Q00124C3Q00013Q00062000013Q000100042Q00368Q00363Q00014Q00363Q00024Q00363Q00034Q00353Q000200012Q005B3Q00013Q00013Q00073Q0003093Q004571756970542Q6F6C026Q00F03F026Q00344003043Q007461736B03043Q0077616974029A5Q99A93F03063Q00506172656E7400204Q006D7Q00206Q00014Q000200018Q0002000100124Q00023Q00122Q000100033Q00122Q000200023Q00044Q0017000100124C000400043Q00206300040004000500122Q000500066Q0004000200014Q000400013Q00202Q0004000400074Q000500023Q00062Q00040013000100050004233Q001300010004233Q001700010004233Q0016000100262100030016000100030004233Q001600012Q005B3Q00013Q0004223Q000800012Q00363Q00013Q00200E5Q00072Q0036000100023Q0006493Q001F000100010004233Q001F00012Q00363Q00034Q0036000100014Q00353Q000200012Q005B3Q00017Q00073Q00030C3Q0057616974466F724368696C6403083Q004261636B7061636B026Q001440030A3Q004368696C64412Q64656403073Q00436F2Q6E656374030C3Q004368696C6452656D6F766564030E3Q00436861726163746572412Q646564001E4Q00397Q00206Q000100122Q000200023Q00122Q000300038Q0003000200064Q001500013Q0004233Q0015000100200E00013Q000400200100010001000500062000033Q000100032Q00363Q00014Q00363Q00024Q00363Q00034Q004700010003000100200E00013Q000600200100010001000500062000030001000100032Q00363Q00014Q00363Q00024Q00363Q00034Q00470001000300012Q003600015Q00200E00010001000700200100010001000500062000030002000100032Q00363Q00014Q00363Q00024Q00363Q00034Q00470001000300012Q005B3Q00013Q00033Q00053Q002Q033Q0049734103043Q00542Q6F6C03043Q007461736B03043Q0077616974029A5Q99B93F01123Q00200100013Q000100120D000300024Q00400001000300020006420001001100013Q0004233Q001100012Q003600015Q00063D0001000B000100010004233Q000B00012Q0036000100013Q0006420001001100013Q0004233Q0011000100124C000100033Q00200600010001000400122Q000200056Q0001000200014Q000100026Q0001000100012Q005B3Q00017Q00053Q002Q033Q0049734103043Q00542Q6F6C03043Q007461736B03043Q0077616974029A5Q99B93F01123Q00200100013Q000100120D000300024Q00400001000300020006420001001100013Q0004233Q001100012Q003600015Q00063D0001000B000100010004233Q000B00012Q0036000100013Q0006420001001100013Q0004233Q0011000100124C000100033Q00200600010001000400122Q000200056Q0001000200014Q000100026Q0001000100012Q005B3Q00017Q00033Q0003043Q007461736B03043Q0077616974027Q0040010D4Q003600015Q00063D00010006000100010004233Q000600012Q0036000100013Q0006420001000C00013Q0004233Q000C000100124C000100013Q00200600010001000200122Q000200036Q0001000200014Q000100026Q0001000100012Q005B3Q00017Q00053Q0003043Q007469636B03043Q007461736B03043Q0077616974027Q0040026Q00144000153Q00120B3Q00018Q000100024Q00018Q00013Q00014Q000200013Q00062Q00020014000100010004233Q001400012Q00448Q0036000100024Q005C0001000100020006420001001400013Q0004233Q0014000100124C000200023Q00201100020002000300122Q000300046Q0002000200014Q000200036Q00020001000100122Q000200056Q000200014Q005B3Q00017Q00013Q00030A3Q00446973636F2Q6E65637400114Q00367Q0006423Q000800013Q0004233Q000800012Q00367Q0020015Q00012Q00353Q000200012Q002C8Q00448Q00363Q00014Q001C3Q000100016Q00028Q000100019Q006Q00039Q008Q00048Q00017Q000F3Q0003043Q007469636B03073Q004B6579436F646503043Q00456E756D2Q033Q00456E6403043Q00486F6D6503063Q0044656C65746503063Q00496E7365727403063Q0050616765557003083Q0050616765446F776E03023Q00463103023Q004632027Q004003023Q004633026Q00F03F026Q00E03F016F3Q00122E000100016Q0001000100024Q00015Q00202Q00013Q000200122Q000200033Q00202Q00020002000200202Q00020002000400062Q0001000C000100020004233Q000C00012Q0036000100014Q00120001000100010004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000500064900010015000100020004233Q001500012Q0036000100024Q00120001000100010004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000600064900010020000100020004233Q002000012Q0036000100034Q00120001000100012Q0036000100044Q00120001000100010004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000700064900010029000100020004233Q002900012Q0036000100054Q00120001000100010004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000800064900010033000100020004233Q003300012Q0036000100064Q000A000100014Q0044000100063Q0004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E0002000200090006490001003D000100020004233Q003D00012Q0036000100074Q000A000100014Q0044000100073Q0004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000A00064900010046000100020004233Q004600012Q0036000100084Q00120001000100010004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000B0006490001005A000100020004233Q005A00012Q0036000100093Q0006420001005200013Q0004233Q005200012Q0036000100044Q00120001000100010004233Q006E00012Q00360001000A4Q005C0001000100022Q0077000200013Q000E67000C006E000100020004233Q006E00012Q00360002000B4Q00120002000100010004233Q006E000100200E00013Q000200124C000200033Q00200E00020002000200200E00020002000D0006490001006E000100020004233Q006E00012Q00360001000C3Q002621000100660001000E0004233Q0066000100120D0001000F4Q00440001000C3Q0004233Q006E00012Q00360001000C3Q0026210001006C0001000F0004233Q006C000100120D0001000C4Q00440001000C3Q0004233Q006E000100120D0001000E4Q00440001000C4Q005B3Q00019Q002Q0001054Q001400018Q00028Q000100026Q00019Q0000019Q003Q00044Q00368Q000A8Q00448Q005B3Q00019Q003Q00044Q00368Q000A8Q00448Q005B3Q00017Q00013Q00027Q0040000E4Q00367Q0006423Q000600013Q0004233Q000600012Q00363Q00014Q00123Q000100010004233Q000D00012Q00363Q00024Q005C3Q000100022Q007700015Q000E670001000D000100010004233Q000D00012Q0036000100034Q00120001000100012Q005B3Q00017Q00033Q0003043Q007479706503063Q006E756D626572028Q0001093Q00124C000100014Q003800026Q006100010002000200262100010008000100020004233Q00080001000E600003000800013Q0004233Q000800012Q00448Q005B3Q00019Q003Q00034Q00368Q00543Q00024Q005B3Q00017Q00033Q0003073Q006379636C696E6703043Q007370616D03083Q00696E616374697665000F4Q00367Q0006423Q000600013Q0004233Q0006000100120D3Q00014Q00543Q00023Q0004233Q000E00012Q00363Q00013Q0006423Q000C00013Q0004233Q000C000100120D3Q00024Q00543Q00023Q0004233Q000E000100120D3Q00034Q00543Q00024Q005B3Q00019Q003Q00054Q005E9Q003Q000100029Q006Q00028Q00017Q00", GetFEnv(), ...);
