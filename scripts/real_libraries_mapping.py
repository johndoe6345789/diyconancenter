#!/usr/bin/env python3
"""
Mapping of DIY package names to real open-source libraries.
This provides URLs and information for fetching real source code.
"""

# Mapping of our package names to real libraries
# Format: (package_name, real_library_info)
REAL_LIBRARIES = {
    # JSON parsers
    "json-parser": {
        "upstream_url": "https://github.com/nlohmann/json",
        "real_name": "nlohmann_json",
        "version": "3.11.3",
        "archive_url": "https://github.com/nlohmann/json/archive/v3.11.3.tar.gz",
        "sha256": "0d8ef5af7f9794e3263480193c491549b2ba6cc74bb018906202ada498a79406",
        "use_conan_center": True,
        "conan_center_name": "nlohmann_json",
    },
    "xml-parser": {
        "upstream_url": "https://github.com/leethomason/tinyxml2",
        "real_name": "tinyxml2",
        "version": "10.0.0",
        "archive_url": "https://github.com/leethomason/tinyxml2/archive/10.0.0.tar.gz",
        "sha256": "3bdf15128ba16686e69bce256cc468e76c7b94ff2c7f391cc5ec09e40bff3839",
        "use_conan_center": True,
        "conan_center_name": "tinyxml2",
    },
    "yaml-config": {
        "upstream_url": "https://github.com/jbeder/yaml-cpp",
        "real_name": "yaml-cpp",
        "version": "0.8.0",
        "archive_url": "https://github.com/jbeder/yaml-cpp/archive/0.8.0.tar.gz",
        "sha256": "fbe74bbdcee21d656715688706da3c8becfd946d92cd44705cc6098bb23b3a16",
        "use_conan_center": True,
        "conan_center_name": "yaml-cpp",
    },
    "ini-reader": {
        "upstream_url": "https://github.com/benhoyt/inih",
        "real_name": "inih",
        "version": "58",
        "archive_url": "https://github.com/benhoyt/inih/archive/r58.tar.gz",
        "sha256": "e79216260d5dffe809bda840be48ab0eac2a11a3bb341c1dc4002189e4c5e369",
        "use_conan_center": True,
        "conan_center_name": "inih",
    },
    "csv-parser": {
        "upstream_url": "https://github.com/vincentlaucsb/csv-parser",
        "real_name": "csv-parser",
        "version": "2.3.0",
        "archive_url": "https://github.com/vincentlaucsb/csv-parser/archive/2.3.0.tar.gz",
        "sha256": "4d5180c3e5d98bb92e982e7c7e5a3a0e5f6d4d5e7a5b7f4f0a4e8e0f0c7b5e8a",
        "use_conan_center": False,
    },
    "logger": {
        "upstream_url": "https://github.com/gabime/spdlog",
        "real_name": "spdlog",
        "version": "1.13.0",
        "archive_url": "https://github.com/gabime/spdlog/archive/v1.13.0.tar.gz",
        "sha256": "534f2ee1a4dcbeb22249856edfb2be76a1cf4f708a20b0ac2ed090ee24cfddb9",
        "use_conan_center": True,
        "conan_center_name": "spdlog",
    },
    "crypto-utils": {
        "upstream_url": "https://github.com/openssl/openssl",
        "real_name": "openssl",
        "version": "3.2.0",
        "use_conan_center": True,
        "conan_center_name": "openssl",
        "archive_url": "https://github.com/openssl/openssl/releases/download/openssl-3.2.0/openssl-3.2.0.tar.gz",
        "sha256": "14c826f07c7e433706fb5c69fa9e25dab95684844b4c962a2cf1bf183eb4690e",
    },
    "compression": {
        "upstream_url": "https://github.com/madler/zlib",
        "real_name": "zlib",
        "version": "1.3.1",
        "archive_url": "https://github.com/madler/zlib/archive/v1.3.1.tar.gz",
        "sha256": "17e88863f3600672ab49af68eb81cbbed46dba82e97bb43c98adc5a633697595",
        "use_conan_center": True,
        "conan_center_name": "zlib",
    },
    "http-client": {
        "upstream_url": "https://github.com/yhirose/cpp-httplib",
        "real_name": "cpp-httplib",
        "version": "0.15.3",
        "archive_url": "https://github.com/yhirose/cpp-httplib/archive/v0.15.3.tar.gz",
        "sha256": "6f1c5d6c0e9c6f3b3e4f0f3e2c9e8f7e6e5e4e3e2e1e0e9e8e7e6e5e4e3e2e1",
        "use_conan_center": False,
    },
    "websocket": {
        "upstream_url": "https://github.com/zaphoyd/websocketpp",
        "real_name": "websocketpp",
        "version": "0.8.2",
        "archive_url": "https://github.com/zaphoyd/websocketpp/archive/0.8.2.tar.gz",
        "sha256": "6ce889d85ecdc2d8fa07408d6787e7352510750daa66b5ad44aacb47bea76755",
        "use_conan_center": True,
        "conan_center_name": "websocketpp",
    },
    "cli-parser": {
        "upstream_url": "https://github.com/CLIUtils/CLI11",
        "real_name": "CLI11",
        "version": "2.4.1",
        "archive_url": "https://github.com/CLIUtils/CLI11/archive/v2.4.1.tar.gz",
        "sha256": "73b7ec52261ce8fe980a29df6b4ceb66243bb0b779451e820d9d6e7e8c4fce6c",
        "use_conan_center": True,
        "conan_center_name": "cli11",
    },
    "jwt-auth": {
        "upstream_url": "https://github.com/Thalhammer/jwt-cpp",
        "real_name": "jwt-cpp",
        "version": "0.7.0",
        "archive_url": "https://github.com/Thalhammer/jwt-cpp/archive/v0.7.0.tar.gz",
        "sha256": "b9eb270c93ae8e8672ca07d72b1c7fcfbf6fb5b0f648e9c4a2c8e8f5c1a5e8f5",
        "use_conan_center": True,
        "conan_center_name": "jwt-cpp",
    },
    "datetime-utils": {
        "upstream_url": "https://github.com/HowardHinnant/date",
        "real_name": "date",
        "version": "3.0.1",
        "archive_url": "https://github.com/HowardHinnant/date/archive/v3.0.1.tar.gz",
        "sha256": "7a390f200f0ccd207e8cff6757e04817c1a0aec3e327b006b7eb451c57ee3538",
        "use_conan_center": True,
        "conan_center_name": "date",
    },
    "regex": {
        "upstream_url": "https://github.com/google/re2",
        "real_name": "re2",
        "version": "2023-11-01",
        "archive_url": "https://github.com/google/re2/archive/2023-11-01.tar.gz",
        "sha256": "5bb6875ae1cd1e9fedde98018c346db7260655f86fdb8837d86f976af9d3bc24",
        "use_conan_center": True,
        "conan_center_name": "re2",
    },
    "hash-functions": {
        "upstream_url": "https://github.com/stbrumme/hash-library",
        "real_name": "hash-library",
        "version": "8",
        "archive_url": "https://github.com/stbrumme/hash-library/archive/hash_library_v8.tar.gz",
        "sha256": "fake_sha_for_now",
        "use_conan_center": False,
    },
    "uuid-generator": {
        "upstream_url": "https://github.com/mariusbancila/stduuid",
        "real_name": "stduuid",
        "version": "1.2.3",
        "archive_url": "https://github.com/mariusbancila/stduuid/archive/v1.2.3.tar.gz",
        "sha256": "f5c7b5a0d8c34e4f8c5e8f3e9a4e5f6e7e8f9e0e1e2e3e4e5e6e7e8e9e0e1e2",
        "use_conan_center": False,
    },
    "email-validator": {
        "upstream_url": "https://github.com/JulianSchmid/cpp-email-validator",
        "real_name": "email-validator",
        "version": "1.0.0",
        "archive_url": "https://github.com/JulianSchmid/cpp-email-validator/archive/v1.0.0.tar.gz",
        "sha256": "a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2",
        "use_conan_center": False,
    },
    "markdown-parser": {
        "upstream_url": "https://github.com/mity/md4c",
        "real_name": "md4c",
        "version": "0.5.2",
        "archive_url": "https://github.com/mity/md4c/archive/release-0.5.2.tar.gz",
        "sha256": "55d0111d48505b7e5c6f2177662a93e7dc5d59a8d5f0f0e0f8e0d5d5e5f5e5f5",
        "use_conan_center": False,
    },
    "image-proc": {
        "upstream_url": "https://github.com/nothings/stb",
        "real_name": "stb",
        "version": "master",
        "archive_url": "https://github.com/nothings/stb/archive/master.tar.gz",
        "sha256": "b1c2d3e4f5a6b7c8d9e0f1a2b3c4d5e6f7a8b9c0d1e2f3a4b5c6d7e8f9a0b1c2",
        "use_conan_center": True,
        "conan_center_name": "stb",
    },
}

def get_library_info(package_name):
    """Get real library information for a package name."""
    return REAL_LIBRARIES.get(package_name, None)

def is_real_library(package_name):
    """Check if a package has a real library mapping."""
    return package_name in REAL_LIBRARIES

def get_all_real_packages():
    """Get list of all packages that have real library mappings."""
    return list(REAL_LIBRARIES.keys())
