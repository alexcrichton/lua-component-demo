y = require('wasi:cli/environment');
stdout = require('wasi:cli/stdout');
random = require('wasi:random/random')
instance_network = require('wasi:sockets/instance-network')
network = require('wasi:sockets/network')
lookup = require('wasi:sockets/ip-name-lookup')

function run(s)
  print('Hello ' .. s .. '!')

  print('env vars:      ' .. dump(y.get_environment()))
  print('wasi CLI args: ' .. dump(y.get_arguments()))
  print('cwd:           ' .. dump(y.initial_cwd()))

  stdout.get_stdout():blocking_write_and_flush('Hello from lua\n')

  print_dns("google.com")
end

function print_dns(domain)
  local n = instance_network.instance_network()
  print("performing DNS lookup for: " .. domain)
  local addresses = lookup.resolve_addresses(n, domain)
  if type(addresses) ~= 'userdata' then
    print('failure to lookup: ' .. network.ErrorCode[addresses])
    return
  end
  while true do
    ::retry::
    local a = addresses:resolve_next_address()
    if a.tag == 'err' then
      if a.val == network.ErrorCode.WouldBlock then
        addresses:subscribe():block()
        goto retry
      else
        error(a.val)
      end
    end
    if a.val == nil then
      break
    end

    local addr = a.val
    if addr.tag == 'ipv4' then
      print('ipv4: ' .. addr.val[1] .. '.' .. addr.val[2] .. '.' .. addr.val[3] .. '.' .. addr.val[4] )
    elseif addr.tag == 'ipv6' then
      local s = ''
      for i=1,8 do
        s = s .. string.format('%04x', addr.val[i])
        if i < 8 then
          s = s .. ':'
        end
      end
      print('ipv6: ' .. s)
    end
  end
end

function dump(o)
   if type(o) == 'table' then
      local s = '{ '
      for k,v in pairs(o) do
         if type(k) ~= 'number' then k = '"'..k..'"' end
         s = s .. '['..k..'] = ' .. dump(v) .. ','
      end
      return s .. '} '
   else
      return tostring(o)
   end
end
