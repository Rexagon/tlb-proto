#[derive(pest_derive::Parser)]
#[grammar = "tlb.pest"]
pub struct Grammar;

#[cfg(test)]
mod tests {
    use pest::Parser;

    use super::*;

    fn check_scheme(scheme: &str) {
        Grammar::parse(Rule::tlb_scheme, scheme).unwrap();
    }

    #[test]
    fn simple_scheme() {
        check_scheme(
            r####"
            unit$_ = Unit;
            true$_ = True;
            // EMPTY False;
            bool_false$0 = Bool;
            bool_true$1 = Bool;
            bool_false$0 = BoolFalse;
            bool_true$1 = BoolTrue;
            nothing$0 {X:Type} = Maybe X;
            just$1 {X:Type} value:X = Maybe X;
            left$0 {X:Type} {Y:Type} value:X = Either X Y;
            right$1 {X:Type} {Y:Type} value:Y = Either X Y;
            pair$_ {X:Type} {Y:Type} first:X second:Y = Both X Y;

            bit$_ (## 1) = Bit;
            "####,
        );
    }

    #[test]
    fn simple_with_constraints() {
        check_scheme(
            r####"
            addr_none$00 = MsgAddressExt;
            addr_extern$01 len:(## 9) external_address:(bits len)
                        = MsgAddressExt;
            anycast_info$_ depth:(#<= 30) { depth >= 1 }
            rewrite_pfx:(bits depth) = Anycast;
            addr_std$10 anycast:(Maybe Anycast)
            workchain_id:int8 address:bits256  = MsgAddressInt;
            addr_var$11 anycast:(Maybe Anycast) addr_len:(## 9)
            workchain_id:int32 address:(bits addr_len) = MsgAddressInt;
            _ _:MsgAddressInt = MsgAddress;
            _ _:MsgAddressExt = MsgAddress;
            "####,
        );
    }

    #[test]
    fn scheme_with_child_cell() {
        check_scheme(
            r####"
            transaction$0111 account_addr:bits256 lt:uint64
            prev_trans_hash:bits256 prev_trans_lt:uint64 now:uint32
            outmsg_cnt:uint15
            orig_status:AccountStatus end_status:AccountStatus
            ^[ in_msg:(Maybe ^(Message Any)) out_msgs:(HashmapE 15 ^(Message Any)) ]
            total_fees:CurrencyCollection state_update:^(HASH_UPDATE Account)
            description:^TransactionDescr = Transaction;
            "####,
        );
    }
}
