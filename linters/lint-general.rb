#!/usr/bin/env ruby

# This script applies basic general linting to a list of source files.
#
# Usage:
#   ./lint-general.rb path1 path2 path3 ...

# Keep track of whether we failed.
failed = false

# Iterate over the input files.
ARGV.each do |path|
  # Print a helpful message.
  puts("Linting file: #{path}")

  # Read the contents of the file.
  lines = File.read(path).split("\n", -1)

  # Iterate over the lines of the file.
  lines.each_with_index do |line, index|
    # Check for tabs, with special behavior for files called `Makefile`.
    if File.basename(path) == 'Makefile'
      # Check for tabs which are not the first character of the line.
      if line =~ /.\t/
        STDERR.puts(
          "Error: Line #{index + 1} of #{path} has a tab in a non-required " \
            "position."
        )
        failed = true
      end
    else
      # Check for any tabs.
      if line =~ /\t/
        STDERR.puts(
          "Error: Line #{index + 1} of #{path} has a tab."
        )
        failed = true
      end
    end

    # Check the line length.
    if line.bytesize > 79
      STDERR.puts(
        "Error: Line #{index + 1} of #{path} has #{line.bytesize} bytes, " \
          "which is more than 79."
      )
      failed = true
    end

    # Check for trailing whitespace.
    if line =~ /\s$/
      STDERR.puts(
        "Error: Line #{index + 1} of #{path} has trailing whitespace."
      )
      failed = true
    end
  end

  # Check for blank lines at the end of the file.
  if !lines.empty?
    # Check that there is a blank line at the end of the file.
    if !lines.last.empty?
      STDERR.puts(
        "Error: #{path} is not terminated by a blank line."
      )
      failed = true
    end

    # Check that there are not multiple blank lines at the end of the file.
    if lines.size > 1
      if lines[lines.size - 2].empty?
        STDERR.puts(
          "Error: #{path} is terminated by more than one blank line."
        )
        failed = true
      end
    end
  end
end

# Fail if necessary.
exit(1) if failed
