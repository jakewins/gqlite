use std::collections::HashMap;
use super::SE1;
use chrono::{DateTime, TimeZone, NaiveDate, NaiveDateTime, Utc};
use rand::{Rng, SeedableRng};
use rand::rngs::{SmallRng};
use crate::backend::t1::SE1Val;

const LDBC_START_YEAR: i32 = 2002;

const LDBC_NUM_CONTINENTS: i64 = 6;
const LDBC_NUM_COUNTRIES: i64 = 1110;
const LDBC_NUM_CITIES: i64 = 1343_0000;

const LDBC_NUM_UNIVERSITIES: i64 = 6380;
const LDBC_NUM_COMPANIES: i64 = 1575;

const LDBC_NUM_TAGS: i64 = 16080;
const LDBC_NUM_TAG_CLASSES: i64 = 71;

pub fn populate(engine: &mut SE1, scale: i64) {

    let num_people = 9892 * scale;

    let mut now = NaiveDate::from_ymd(LDBC_START_YEAR, 1, 1).and_hms(0, 0, 0);
    let days_of_activity = 365 * 10;

    let mut random = SmallRng::seed_from_u64(1337);

    populate_static_data(engine, &mut random);

}

fn populate_static_data(engine: &mut SE1, random: &mut SmallRng) {
    pop_000_places(engine, random);
}

fn pop_000_places(engine: &mut SE1, random: &mut SmallRng) {

    let rt_is_part_of = engine.rt_get_or_create(b"IS_PART_OF");

    let lbl_continent = engine.lbl_get_or_create(b"Continent");
    let lbl_country = engine.lbl_get_or_create(b"Country");
    let lbl_city = engine.lbl_get_or_create(b"City");

    let propk_name = engine.propk_get_or_create(b"name");
    let propk_uri = engine.propk_get_or_create(b"uri");

    let mut continents: HashMap<i64, u64> = HashMap::new();
    let mut countries: HashMap<i64, u64> = HashMap::new();

    for i in 0..LDBC_NUM_CONTINENTS {
        let c = engine.node_create(&[lbl_continent]);
        continents.insert(i, c);
        // engine.node_prop_set(c, propk_name, SE1Val::String(format!("Continent-{}", i)));
        // engine.node_prop_set(c, propk_uri, SE1Val::String(format!("https://continents.com/Continent-{}", i)));
    }

    for i in 0..LDBC_NUM_COUNTRIES {
        let country_id = engine.node_create(&[lbl_country]);
        countries.insert(i, country_id);
        // engine.node_prop_set(country_id, propk_name, SE1Val::String(format!("Country-{}", i)));
        // engine.node_prop_set(country_id, propk_uri, SE1Val::String(format!("https://countries.com/Country-{}", i)));

        let continent_id = if i < LDBC_NUM_CONTINENTS {
            continents[&i]
        } else {
            continents[&random.gen_range(0, LDBC_NUM_CONTINENTS)]
        };

        engine.rel_create(country_id, continent_id, rt_is_part_of);
    }


    for i in 0..LDBC_NUM_CITIES {
        let city_id = engine.node_create(&[lbl_city]);
        // engine.node_prop_set(city_id, propk_name, SE1Val::String(format!("City-{}", i)));
        // engine.node_prop_set(city_id, propk_uri, SE1Val::String(format!("https://cities.com/City-{}", i)));

        let country_id = if i < LDBC_NUM_COUNTRIES {
            countries[&i]
        } else {
            countries[&random.gen_range(0, LDBC_NUM_COUNTRIES)]
        };

        if i % 10_000 == 0 {
            println!("{} / {}", i, LDBC_NUM_CITIES)
        }

        engine.rel_create(city_id, country_id, rt_is_part_of);
    }
}