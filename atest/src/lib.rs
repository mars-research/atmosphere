//! Provides `#[test]` and logs the name of the test with `log`.

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::ToTokens;
use syn::{parse_quote, parse_macro_input, Item};

#[proc_macro_attribute]
pub fn test(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = match parse_macro_input!(item as Item) {
        Item::Fn(f) => f,
        _ => panic!("The #[test] attribute can only be applied to functions"),
    };

    let ident = &func.sig.ident.to_string();

    func.block.stmts.insert(0, parse_quote! {
        log::info!("Running {}", #ident);
    });

    func.block.stmts.push(parse_quote! {
        log::info!("➡️ Success");
    });

    func.attrs.push(parse_quote! {
        #[test_case]
    });

    eprintln!("func: {:?}", func.sig.ident);
    func.into_token_stream().into()
}
