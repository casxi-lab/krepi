use super::*;

/// A fault trace of the prototype kernel: the register record, one frame and
/// the stop record, which an exception record before them and a halt after
/// them complete.
const HEADER: &str = "CASXI_DIAG build_id=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa source=exception pc=0x0000000000004000 sp=0x0000000000001000 fp=0x0000000000001100 lr=0x0000000000005000 process=none thread=none epoch=none";
const FRAME: &str = "CASXI_BT index=0 fp=0x0000000000001100 lr=0x0000000000005000";
const STOP: &str = "CASXI_TRACE frames=1 stop=end stop_fp=0x0000000000000000";
/// The breakpoint exception record whose ELR is the PC of [`HEADER`].
const EXCEPTION: &str = "CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000000004000";

/// A complete object record.
const OBJECT: &[u8] = b"CASXI_OBJECTS cycle=1 selftest=PASS checks=18 root_process=1 root_thread=2 processes=1 threads=1 reserved_processes=2 reserved_threads=2 temporary_generation=14 created_processes=7 reaped_processes=6";

/// A CPU identity record of an Arm Cortex-A76, r4p1.
const RECORD: &[u8] = b"CASXI_CPU model=cortex-a76 midr=0x00000000414fd0b1\r\n";

/// A complete trace transcript: the exception, the trace and the halt.
fn transcript() -> String {
    format!("{EXCEPTION}\n{HEADER}\n{FRAME}\n{STOP}\nCASXI_HALTED")
}

/// `content` with every `from` replaced by `to`.
fn replaced(content: &[u8], from: &str, to: &str) -> Vec<u8> {
    String::from_utf8_lossy(content)
        .replace(from, to)
        .into_bytes()
}

fn feed_all(lines: &[&[u8]]) -> Result<bool, Failure> {
    let mut check = DiagnosticCheck::new();
    let mut halted = false;
    for line in lines {
        halted = check.feed(line)?;
    }
    Ok(halted)
}

#[test]
fn complete_trace_is_accepted_and_rendered() {
    let mut check = DiagnosticCheck::new();
    assert_eq!(check.feed(HEADER.as_bytes()), Ok(false));
    assert_eq!(check.feed(FRAME.as_bytes()), Ok(false));
    assert!(check.result().is_err());
    assert_eq!(check.feed(STOP.as_bytes()), Ok(false));
    assert_eq!(check.feed(b"CASXI_HALTED"), Ok(true));
    let result = check.result().unwrap();
    assert_eq!(result["registers"]["pc"], "0000000000004000");
    assert_eq!(result["frames"].as_array().map(Vec::len), Some(1));
    assert_eq!(result["stop"]["reason"], "end");
    assert_eq!(check.feed(b""), Err(Failure::new("Output after HALTED")));
}

#[test]
fn trace_rules_reject_wrong_frames_stops_and_halts() {
    let (header, frame, stop) = (HEADER.as_bytes(), FRAME.as_bytes(), STOP.as_bytes());
    let frame_1200 = replaced(frame, "1100", "1200");
    assert_eq!(
        feed_all(&[header, &frame_1200]),
        Err(Failure::new("First frame does not match saved FP"))
    );
    let unknown = replaced(stop, "stop=end", "stop=unknown");
    let false_end = replaced(
        stop,
        "stop_fp=0x0000000000000000",
        "stop_fp=0x0000000000001100",
    );
    for wrong in [&unknown[..], &false_end[..]] {
        assert_eq!(
            feed_all(&[header, frame, wrong]),
            Err(Failure::new("Invalid trace stop reason/bound"))
        );
    }
    assert_eq!(
        feed_all(&[header, frame, b"CASXI_HALTED"]),
        Err(Failure::new("Unexpected diagnostic output: CASXI_HALTED"))
    );
    assert_eq!(
        feed_all(&[header, frame, stop, b"CASXI_HALTED", b"CASXI_HALTED"]),
        Err(Failure::new("Output after HALTED"))
    );
    assert_eq!(
        feed_all(&[header, frame, frame]),
        Err(Failure::new(
            "Invalid trace sequence, frame alignment or depth"
        ))
    );
    let wrong_count = replaced(stop, "frames=1", "frames=2");
    assert_eq!(
        feed_all(&[header, frame, &wrong_count]),
        Err(Failure::new("Trace stop count mismatch or duplicate"))
    );
    assert_eq!(
        feed_all(&[frame]),
        Err(Failure::new(
            "Expected build-bound raw register record: CASXI_BT index=0 fp=0x0000000000001100 lr=0x0000000000005000"
        ))
    );
}

#[test]
fn object_records_require_every_field_once() {
    let fields = object_fields(OBJECT).unwrap();
    assert_eq!(object_field(&fields, "root_process"), Some("1"));
    assert_eq!(fields.len(), 12);
    let text = String::from_utf8_lossy(OBJECT);
    let cases = [
        (
            text.replace(" root_process=1", ""),
            "Missing/duplicate/unexpected object fields",
        ),
        (
            format!("{text} root_process=1"),
            "Missing/duplicate/unexpected object fields",
        ),
        (
            text.replace("root_process=1", "root_process=0"),
            "Missing retained root/reserve/selftest coverage",
        ),
        (
            text.replace("cycle=1", "cycle=-1"),
            "Invalid object field cycle",
        ),
        (text.replace("cycle=1", "cycle"), "Malformed object record"),
    ];
    for (raw, message) in cases {
        assert_eq!(
            object_fields(raw.as_bytes()),
            Err(Failure::new(message)),
            "{raw}"
        );
    }
    assert_eq!(
        split_lines(b"a\r\nb\rc\n\nd"),
        vec![&b"a"[..], b"b", b"c", b"", b"d"]
    );
    assert_eq!(
        build_ids(b"x CASXI_BUILD build_id=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n").len(),
        1
    );
}

#[test]
fn trace_transcripts_bind_exception_and_halt() {
    let raw = [
        format!("{EXCEPTION}\n").as_bytes(),
        HEADER.as_bytes(),
        b"\n",
        FRAME.as_bytes(),
        b"\n",
        STOP.as_bytes(),
        b"\nCASXI_HALTED",
    ]
    .concat();
    let result = trace(&raw, "exception", true).unwrap();
    assert_eq!(result["frames"][0]["fp"].as_u64(), Some(0x1100));
    let text = String::from_utf8_lossy(&raw).into_owned();
    assert_eq!(
        trace(
            text.replace("CASXI_HALTED", "").as_bytes(),
            "exception",
            true
        ),
        Err(Failure::new("Wrong trace halt boundary"))
    );
    assert_eq!(
        trace(
            format!("{text}\nCASXI_HALTED").as_bytes(),
            "exception",
            true
        ),
        Err(Failure::new("Output after HALTED"))
    );
    assert_eq!(
        trace(
            text.replace("pc=0x0000000000004000", "pc=0x0000000000004004")
                .as_bytes(),
            "exception",
            true
        ),
        Err(Failure::new("Raw exception ELR and diagnostic PC differ"))
    );
    assert_eq!(
        trace(
            text.replace("source=exception", "source=probe").as_bytes(),
            "exception",
            true
        ),
        Err(Failure::new("Wrong trace source"))
    );
    assert_eq!(
        trace(format!("{text}\n{HEADER}").as_bytes(), "exception", true),
        Err(Failure::new("Missing/duplicate diagnostic header"))
    );
}

#[test]
fn lines_strip_one_carriage_return() {
    let found: Vec<_> = lines(b"a\r\nb\nc").collect();
    assert_eq!(found, vec![(0, &b"a"[..], 3), (3, &b"b"[..], 5)]);
}

#[test]
fn ready_requires_a_complete_line() {
    assert_eq!(
        ready(b"boot\r\nCASXI_READY\r\n").map(|m| (m.start, m.end)),
        Some((6, 19))
    );
    assert!(ready(b"CASXI_READY").is_none());
    assert!(ready(b"xCASXI_READY\n").is_none());
}

#[test]
fn brk_exception_captures_the_link_register() {
    let line = b"CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000040200f10 extra\r\n";
    let found = brk_exception(line).expect("match");
    assert_eq!(found.captures, vec![b"0000000040200f10".to_vec()]);
    assert!(
        brk_exception(b"CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000040200f1\n")
            .is_none()
    );
    assert!(
        brk_exception(b"CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000040200f10x\n")
            .is_none()
    );
}

/// One record of an Arm Cortex-A76 is accepted, whatever its variant and
/// revision; no record, a record of another part and a record that is not
/// one are rejected. An invalid record is written with its quote and its
/// control byte escaped; the newline ends the record.
#[test]
fn cpu_identity_requires_one_arm_cortex_a76_record() {
    let record = b"boot\r\nCASXI_CPU model=cortex-a76 midr=0x00000000414fd0b1\r\nCASXI_READY\r\n";
    assert_eq!(
        check_cpu_identity(record).unwrap(),
        ("cortex-a76".to_string(), "0x00000000414fd0b1".to_string())
    );
    assert!(check_cpu_identity(b"CASXI_READY\n").is_err());
    assert!(check_cpu_identity(b"CASXI_CPU model=cortex-a76 midr=0x00000000414fd03f\n").is_err());
    assert_eq!(
        check_cpu_identity(b"CASXI_CPU a'\x01\n"),
        Err(Failure::new(
            "Invalid CPU identity record: CASXI_CPU a\\'\\x01"
        ))
    );
}

#[test]
fn a_cpu_identity_among_boot_output_is_accepted() {
    let output = [&b"boot\r\n"[..], RECORD, &b"CASXI_READY\r\n"[..]].concat();
    assert_eq!(
        check_cpu_identity(&output).unwrap(),
        ("cortex-a76".to_string(), "0x00000000414fd0b1".to_string())
    );
}

#[test]
fn variant_and_revision_are_not_part_of_the_cpu_identity() {
    let record = replaced(RECORD, "414fd0b1", "410fd0bf");
    assert_eq!(check_cpu_identity(&record).unwrap().0, "cortex-a76");
}

#[test]
fn missing_duplicate_or_malformed_cpu_identity_records_are_rejected() {
    let cases: Vec<(Vec<u8>, &str)> = vec![
        (
            b"CASXI_READY\n".to_vec(),
            "Expected one CPU identity record, got 0",
        ),
        (
            [RECORD, RECORD].concat(),
            "Expected one CPU identity record, got 2",
        ),
        (
            replaced(RECORD, "cortex-a76", "cortex-a53"),
            "Invalid CPU identity record: CASXI_CPU model=cortex-a53 midr=0x00000000414fd0b1",
        ),
        (
            replaced(RECORD, "414fd0b1", "414fd03f"),
            "CPU identity is not Arm Cortex-A76: MIDR=0x00000000414fd03f",
        ),
        (
            replaced(RECORD, "414fd0b1", "514fd0b1"),
            "CPU identity is not Arm Cortex-A76: MIDR=0x00000000514fd0b1",
        ),
        (
            replaced(RECORD, "414fd0b1", "414fd0bg"),
            "Invalid CPU identity record: CASXI_CPU model=cortex-a76 midr=0x00000000414fd0bg",
        ),
        (
            [RECORD.strip_suffix(b"\r\n").unwrap(), b" extra=1\n"].concat(),
            "Invalid CPU identity record: CASXI_CPU model=cortex-a76 midr=0x00000000414fd0b1 extra=1",
        ),
        (
            [RECORD, b"CASXI_CPU malformed\n"].concat(),
            "Expected one CPU identity record, got 2",
        ),
    ];
    for (output, message) in cases {
        assert_eq!(
            check_cpu_identity(&output),
            Err(Failure::new(message)),
            "{}",
            output.escape_ascii()
        );
    }
}

#[test]
fn a_complete_object_record_is_accepted_in_record_order() {
    let fields = object_fields(OBJECT).unwrap();
    let names: Vec<&str> = fields.iter().map(|(k, _)| k.as_str()).collect();
    assert_eq!(names[..3], ["cycle", "selftest", "checks"]);
    assert_eq!(object_field(&fields, "root_process"), Some("1"));
    assert_eq!(object_field(&fields, "temporary_generation"), Some("14"));
    assert_eq!(fields_value(&fields)["checks"], "18");
}

#[test]
fn object_records_with_omitted_duplicate_or_invalid_fields_are_rejected() {
    let text = String::from_utf8_lossy(OBJECT).into_owned();
    let cases = [
        (
            text.replace(" root_process=1", ""),
            "Missing/duplicate/unexpected object fields",
        ),
        (
            format!("{text} root_process=1"),
            "Missing/duplicate/unexpected object fields",
        ),
        (
            format!("{text} extra=1"),
            "Missing/duplicate/unexpected object fields",
        ),
        (
            text.replace("root_process=1", "root_process=0"),
            "Missing retained root/reserve/selftest coverage",
        ),
        (
            text.replace("checks=18", "checks=17"),
            "Missing retained root/reserve/selftest coverage",
        ),
        (
            text.replace("cycle=1", "cycle=-1"),
            "Invalid object field cycle",
        ),
        (
            text.replace("threads=1", "threads=18446744073709551616"),
            "Invalid object field threads",
        ),
        (text.replace("cycle=1", "cycle"), "Malformed object record"),
    ];
    for (raw, expected) in cases {
        assert_eq!(
            object_fields(raw.as_bytes()),
            Err(Failure::new(expected)),
            "{raw}"
        );
    }
}

#[test]
fn a_complete_trace_transcript_binds_the_exception_and_the_halt() {
    let result = trace(transcript().as_bytes(), "exception", true).unwrap();
    assert_eq!(result["registers"]["pc"], "0000000000004000");
    assert_eq!(result["frames"][0]["fp"].as_u64(), Some(0x1100));
    assert_eq!(result["stop"]["reason"], "end");
    // A live probe trace has no halt and no raw exception record.
    let live = format!(
        "{}\n{FRAME}\n{STOP}\n",
        HEADER.replace("source=exception", "source=probe")
    );
    assert!(trace(live.as_bytes(), "probe", false).is_ok());
}

#[test]
fn trace_transcripts_with_wrong_frames_stops_halts_or_identities_are_rejected() {
    let raw = transcript();
    let cases = [
        (
            raw.replace(FRAME, &FRAME.replace("1100", "1200")),
            "First frame does not match saved FP",
        ),
        (
            raw.replace("stop=end", "stop=unknown"),
            "Invalid trace stop reason/bound",
        ),
        (
            raw.replace("stop_fp=0x0000000000000000", "stop_fp=0x0000000000001100"),
            "Invalid trace stop reason/bound",
        ),
        (raw.replace("CASXI_HALTED", ""), "Wrong trace halt boundary"),
        (format!("{raw}\nCASXI_HALTED"), "Output after HALTED"),
        (
            raw.replace("pc=0x0000000000004000", "pc=0x0000000000004004"),
            "Raw exception ELR and diagnostic PC differ",
        ),
        (
            raw.replace("source=exception", "source=probe"),
            "Wrong trace source",
        ),
        (
            format!("{raw}\n{HEADER}"),
            "Missing/duplicate diagnostic header",
        ),
    ];
    for (text, expected) in cases {
        assert_eq!(
            trace(text.as_bytes(), "exception", true),
            Err(Failure::new(expected)),
            "{text}"
        );
    }
}

#[test]
fn a_fatal_breakpoint_record_is_bound_to_its_trace_and_halt() {
    let record = brk_exception(format!("{EXCEPTION}\n").as_bytes()).expect("exception record");
    let elr = hex_value(&String::from_utf8_lossy(&record.captures[0]));
    let (header, frame, stop) = (HEADER.as_bytes(), FRAME.as_bytes(), STOP.as_bytes());
    let mut check = DiagnosticCheck::new();
    for line in [header, frame, stop] {
        assert_eq!(check.feed(line), Ok(false));
    }
    assert_eq!(check.feed(b"CASXI_HALTED"), Ok(true));
    let registers = check.registers().expect("registers");
    assert_eq!(registers.source, "exception");
    assert_eq!(hex_value(&registers.pc), elr);
    let result = check.result().unwrap();
    assert_eq!(result["frames"][0]["fp"].as_u64(), Some(0x1100));
    assert_eq!(
        check.feed(b"late"),
        Err(Failure::new("Output after HALTED"))
    );

    // A probe record or a different program counter would not bind the BRK.
    let mut other = DiagnosticCheck::new();
    other
        .feed(&replaced(header, "source=exception", "source=probe"))
        .unwrap();
    assert_eq!(other.registers().unwrap().source, "probe");
    let mut moved = DiagnosticCheck::new();
    moved
        .feed(&replaced(
            header,
            "pc=0x0000000000004000",
            "pc=0x0000000000004004",
        ))
        .unwrap();
    assert_ne!(hex_value(&moved.registers().unwrap().pc), elr);
    // An incomplete trace has no result; a frame that skips the saved FP is
    // rejected.
    let mut partial = DiagnosticCheck::new();
    partial.feed(header).unwrap();
    assert_eq!(partial.result(), Err(Failure::new("Incomplete trace")));
    assert_eq!(
        partial.feed(&replaced(frame, "1100", "1200")),
        Err(Failure::new("First frame does not match saved FP"))
    );
}

/// A record is found only once its terminator has arrived: no prefix of a
/// summary line or of a stage line of the prototype's recovery records,
/// however much of the record it holds, yields a line, and the whole line
/// yields exactly one.
#[test]
fn a_record_is_found_only_once_its_line_is_complete() {
    let summary: &[u8] =
        b"CASXI_RECOVERY version=1 cycle=1 status=PASS owner=EL0 reclaim=PASS operation=4\n";
    let is_summary = |content: &[u8]| {
        content
            .starts_with(b"CASXI_RECOVERY version=1 cycle=")
            .then(Vec::new)
    };
    for end in 0..summary.len() {
        assert!(
            find_line(&summary[..end], is_summary).is_none(),
            "prefix {end}"
        );
    }
    assert_eq!(
        find_line(summary, is_summary),
        Some(Match {
            start: 0,
            end: summary.len(),
            captures: Vec::new(),
        })
    );

    let stage: &[u8] = b"CASXI_RECOVERY_STAGE v=1 phase=4 nonce=0x51 value=2 checksum=2909735437\n";
    let stages_in = |buffer: &[u8]| -> Vec<Vec<u8>> {
        lines(buffer)
            .filter(|(_, content, _)| content.starts_with(b"CASXI_RECOVERY_STAGE "))
            .map(|(_, content, _)| content.to_vec())
            .collect()
    };
    for end in 0..stage.len() {
        assert!(stages_in(&stage[..end]).is_empty(), "prefix {end}");
    }
    assert_eq!(
        stages_in(stage),
        [stage.strip_suffix(b"\n").unwrap().to_vec()]
    );
}

/// Fields are separated by the ASCII white space of `u8::is_ascii_whitespace`,
/// the form feed among it, but not by a vertical tab, which stays inside its
/// token.
#[test]
fn fields_split_at_ascii_white_space_but_not_at_a_vertical_tab() {
    let expected = vec![
        ("a".to_string(), "1".to_string()),
        ("b".to_string(), "2".to_string()),
    ];
    for separator in [" ", "\t", "\r", "\n", "\x0c", " \t "] {
        let line = format!("CASXI_X a=1{separator}b=2");
        assert_eq!(
            parse_fields(line.as_bytes(), "CASXI_X", &["a", "b"]),
            Ok(expected.clone()),
            "{}",
            line.escape_debug()
        );
    }
    assert_eq!(
        parse_fields(b"CASXI_X a=1\x0bb=2", "CASXI_X", &["a", "b"]),
        Err(Failure::new("Unexpected CASXI_X fields: [\"a\"]"))
    );
    assert_eq!(
        parse_fields(b"CASXI_X a=1\x0bb=2", "CASXI_X", &["a"]),
        Ok(vec![("a".to_string(), "1\x0bb=2".to_string())])
    );
    assert_eq!(
        parse_fields(b"CASXI_Y a=1", "CASXI_X", &["a"]),
        Err(Failure::new("Missing CASXI_X record"))
    );
    assert_eq!(
        parse_fields(b"CASXI_X a=\xce\x9e", "CASXI_X", &["a"]),
        Err(Failure::new("Non-ASCII CASXI_X record"))
    );
}

/// A rejected token or record is written with the escapes of
/// `<[u8]>::escape_ascii`, and the names of a record with unexpected fields
/// in Rust's debug form, sorted by their bytes.
#[test]
fn rejected_tokens_records_and_field_names_are_written_with_escapes() {
    assert_eq!(
        parse_fields(b"CASXI_X it's", "CASXI_X", &["a"]),
        Err(Failure::new("Malformed CASXI_X field: it\\'s"))
    );
    assert_eq!(
        parse_fields(b"CASXI_X \"a\"\\\x7f", "CASXI_X", &["a"]),
        Err(Failure::new("Malformed CASXI_X field: \\\"a\\\"\\\\\\x7f"))
    );
    assert_eq!(
        parse_fields(b"CASXI_X a= b=2", "CASXI_X", &["a", "b"]),
        Err(Failure::new("Empty or duplicate field: a="))
    );
    assert_eq!(
        parse_fields(b"CASXI_X a=1 a=2", "CASXI_X", &["a"]),
        Err(Failure::new("Empty or duplicate field: a=2"))
    );
    assert_eq!(
        parse_fields(b"CASXI_X it's=1 c\x01=2 a\\b=3", "CASXI_X", &["x"]),
        Err(Failure::new(
            "Unexpected CASXI_X fields: [\"a\\\\b\", \"c\\u{1}\", \"it's\"]"
        ))
    );
    assert_eq!(
        parse_fields(b"CASXI_X", "CASXI_X", &["x"]),
        Err(Failure::new("Unexpected CASXI_X fields: []"))
    );
    assert_eq!(
        check_cpu_identity(b"CASXI_CPU it's\r\n"),
        Err(Failure::new(
            "Invalid CPU identity record: CASXI_CPU it\\'s"
        ))
    );
}
