#!/usr/bin/env ruby

# This script checks for unused or unsorted imports. The build command should
# have a '?' indicating where the path should be inserted.
#
# Usage:
#   ./lint-imports.rb import-regex build-command path1 path2 path3 ...

require 'open3'
require 'securerandom'

# Make sure we got enough arguments.
if ARGV.size < 2
  STDERR.puts(
    'Usage: ./lint-imports.rb import-regex build-command path1 path2 path3 ...'
  )
  exit(1)
end

# Parse the input.
importRegexStr, buildCommand, *paths = ARGV
importRegex = Regexp.new(importRegexStr, nil)

# Make sure the build command has exactly one '?'.
if buildCommand.count('?') != 1
  STDERR.puts("Error: #{ARGV[1]}")
  exit(1)
end

# Keep track of whether we failed.
failed = false

# Iterate over the input files.
paths.each do |path|
  # Print a helpful message.
  puts("Checking file for unused or unsorted imports: #{path}")

  # Read the contents of the file.
  lines = File.read(path).split("\n", -1)

  # Get the imports.
  imports = lines.map.with_index do |line, index|
    [line, index]
  end.select do
    |line, index| line =~ importRegex
  end

  # Check that the imports are sorted.
  if imports.sort { |a, b| a[0] <=> b[0]} != imports
    STDERR.puts("Error: unsorted imports in #{path}.")
    imports.each { |import, index| STDERR.puts("  #{import}") }
    failed = true
  end

  # Delete each import and try to rebuild the file without it.
  imports.each do |import, index|
    uniqueId = SecureRandom.hex
    mutatedLines = lines.clone
    mutatedLines.delete_at(index)
    mutatedFileContents = mutatedLines.join("\n")
    mutatedFilePath = path.dup.insert(path.rindex('.') || -1, uniqueId)
    begin
      File.write(mutatedFilePath, mutatedFileContents)
      _, _, status = Open3.capture3(buildCommand.sub('?', mutatedFilePath))
      if status.success?
        STDERR.puts("Error: unused import in #{path}.")
        STDERR.puts("  #{import}")
        failed = true
      end
    ensure
      Dir.glob(
        File.join(File.dirname(path), '*'),
        File::FNM_DOTMATCH
      ).each do |filePath|
        File.delete(filePath) if filePath.include?(uniqueId)
      end
    end
  end
end

# Fail if necessary.
exit(1) if failed
