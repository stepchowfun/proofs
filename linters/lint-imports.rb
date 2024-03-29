#!/usr/bin/env ruby

# This script checks for unused or unsorted imports. The build command should
# have a '?' indicating where the path should be inserted.
#
# Usage:
#   ./lint-imports.rb
#     import-matching-regex
#     import-validation-regex
#     build-command
#     path1 path2 path3 ...

require 'open3'
require 'securerandom'

# Make sure we got enough arguments.
if ARGV.size < 3
  STDERR.puts(
    'Usage: ./lint-imports.rb ' +
      'import-matching-regex ' +
      'import-validation-regex ' +
      'build-command ' +
      'path1 path2 path3 ...'
  )
  exit(1)
end

# Parse the input.
import_matching_regex_str, import_validation_regex_str, build_command, *paths =
  ARGV
import_matching_regex = Regexp.new(import_matching_regex_str, nil)
import_validation_regex = Regexp.new(import_validation_regex_str, nil)

# Make sure the build command has exactly one '?'.
if build_command.count('?') != 1
  STDERR.puts("Error: invalid build command `#{build_command}`")
  exit(1)
end

# Keep track of whether we failed.
failed = false

# Iterate over the input files.
paths.each do |path|
  # Print a helpful message.
  puts("Checking file for unused or unsorted imports: #{path}")

  # Read the contents of the file.
  original_file_contents = File.read(path)
  lines = original_file_contents.split("\n", -1)

  # Get the imports.
  imports = lines.map.with_index do |line, index|
    [line, index]
  end.select do |line, index|
    line =~ import_matching_regex
  end

  # Validate the imports.
  imports.each do |import, _|
    if !import_validation_regex.match?(import)
      STDERR.puts("Error: invalid import in #{path}.")
      STDERR.puts("  #{import}")
      failed = true
    end
  end

  # Check that the imports are sorted.
  if imports.sort { |a, b| a[0] <=> b[0]} != imports
    STDERR.puts("Error: unsorted imports in #{path}.")
    imports.each { |import, _| STDERR.puts("  #{import}") }
    failed = true
  end

  # Delete each import and try to rebuild the file without it.
  imports.each do |import, index|
    unique_id = SecureRandom.hex
    clone_file_path = path.dup.insert(
      path.rindex('.') || -1,
      "clone_#{unique_id}",
    )
    mutated_file_path = path.dup.insert(
      path.rindex('.') || -1,
      "mutated_#{unique_id}",
    )
    mutated_lines = lines.clone
    mutated_lines.delete_at(index)
    mutated_file_contents = mutated_lines.join("\n")
    begin
      File.write(clone_file_path, original_file_contents)
      stdout, stderr, status = Open3.capture3(
        build_command.sub('?', clone_file_path)
      )
      if !status.success?
        STDERR.puts("Error: there is a bug in the linter configuration.")
        STDERR.puts("Unable to compile #{path}.")
        STDERR.puts("STDOUT:")
        STDERR.puts(stdout)
        STDERR.puts("STDERR:")
        STDERR.puts(stderr)
        failed = true
      end

      File.write(mutated_file_path, mutated_file_contents)
      _, _, status = Open3.capture3(build_command.sub('?', mutated_file_path))
      if status.success?
        STDERR.puts("Error: unused import in #{path}.")
        STDERR.puts("  #{import}")
        failed = true
      end
    ensure
      Dir.glob(
        File.join(File.dirname(path), '*'),
        File::FNM_DOTMATCH
      ).each do |file_path|
        File.delete(file_path) if file_path.include?(unique_id)
      end
    end
  end
end

# Fail if necessary.
exit(1) if failed
