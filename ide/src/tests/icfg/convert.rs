use crate::icfg::convert::Convert;
use crate::icfg::graphviz::render_to;
use insta::assert_snapshot;
use std::io::Cursor;

macro_rules! ir {
    ($name:expr, $ir:expr) => {
        let mut convert = Convert::new();

        let res = convert.visit($ir).unwrap();

        assert_snapshot!($name, format!("{:#?}", res));

        //let mut dot = String::new();
        let mut dot = Cursor::new(Vec::new());
        render_to(&res, &mut dot);

        assert_snapshot!(
            format!("{}_dot", $name),
            std::str::from_utf8(dot.get_ref()).unwrap()
        );
    };
}

#[test]
fn test_ir_const() {
    ir!(
        "test_ir_const",
        "
         define test {
            %0 = 1
         };
    "
    );
}

#[test]
fn test_ir_double_const() {
    ir!(
        "test_ir_const",
        "
         define test {
            %0 = 1
            %1 = 1
         };
    "
    );
}
