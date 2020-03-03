fn main() -> anyhow::Result<()> {
    #[cfg(all(feature = "cli", feature = "gram"))]
    {
        use clap::{App, AppSettings};
        use gqlite::{Cursor, Database};
        use std::fs::OpenOptions;

        let matches = App::new("g")
            .version("0.0")
            .about("A graph database in a gram file!")
            .setting(AppSettings::ArgRequiredElseHelp)
            .args_from_usage(
                "-f, --file=[FILE] @graph.gram 'Sets the gram file to use'
            -h, --help 'Print help information'
            <QUERY> 'Query to execute'",
            )
            .get_matches();

        let query_str = matches.value_of("QUERY").unwrap();
        let path = matches.value_of("file").unwrap_or("graph.gram");
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(path)?;
        let mut db = Database::open(file)?;
        let mut cursor = Cursor::new();
        db.run(query_str, &mut cursor)?;

        while cursor.next()? {}
    }

    Ok(())
}
